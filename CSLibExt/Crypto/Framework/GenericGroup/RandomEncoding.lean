/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import CSLibExt.Crypto.Framework.GenericGroup
public import Mathlib.Data.Fintype.Pi

/-!
# Generic group experiments with random bit-string identifiers

In exponent coordinates relative to a generator, the group law is addition in `ZMod N`.
A single hidden injection labels this group for the whole experiment. The strategy sees the
labels of `1` and the secret, followed by the label returned by each call it makes. It may use
any function of these bit strings, but may use only previously obtained identifiers as operands.

Source: A. V. Sutherland, *18.783 Elliptic Curves*, MIT, Spring 2013, Lecture 11, §11.1,
Theorem 11.1 and its proof (pp. 1–3), presenting a bound due to V. Shoup.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup.RandomEncoding

open Cslib.Probability.PMF (uniformOfFintype)
open scoped ENNReal

/-- Assign a distinct `n`-bit word to each group element; unused words are allowed. -/
abbrev Encoding (N n : ℕ) := ZMod N ↪ (Fin n → Bool)

/-- With enough words, all injections form a nonempty sample space. -/
theorem encoding_nonempty {N n : ℕ} [NeZero N] (hcap : N ≤ 2 ^ n) : Nonempty (Encoding N n) :=
  Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_fun, ZMod.card] using hcap)

/-- One black-box call when `k` identifiers have been obtained. Indices name occurrences:
there need not be `k` distinct labels. -/
inductive Call (k : ℕ) where
  | identity
  | inverse (i : Fin k)
  | compose (i j : Fin k)

/-- Interpret a call on the hidden group elements underlying the obtained identifiers. -/
def Call.value {N k : ℕ} (env : Fin k → ZMod N) : Call k → ZMod N
  | .identity => 0
  | .inverse i => -env i
  | .compose i j => env i + env j

/-- A bounded interaction after `k` identifiers have been obtained, with `q` calls left.
A continuation receives the actual answer word and may retain the entire earlier history in
its closure. Returning early is allowed at every budget. -/
inductive Interaction (N n : ℕ) : (k q : ℕ) → Type where
  | output {k q} (y : ZMod N) : Interaction N n k q
  | query {k q} (op : Call k) (next : (Fin n → Bool) → Interaction N n (k + 1) q) :
      Interaction N n k (q + 1)

/-- Run the interaction with one fixed encoding. Return its output and the number of calls
actually made. Only the encoded answer, not `env` or `enc`, is passed to the continuation. -/
def Interaction.run {N n k q : ℕ} (enc : Encoding N n) (env : Fin k → ZMod N) :
    Interaction N n k q → ZMod N × ℕ
  | .output y => (y, 0)
  | .query op next =>
    let v := op.value env
    let (y, cost) := (next (enc v)).run enc (snocEnv env v)
    (y, cost + 1)

/-- The cost recorded on each execution path respects the interaction's budget. -/
theorem Interaction.run_cost_le {N n k q : ℕ} (t : Interaction N n k q) (enc : Encoding N n)
    (env : Fin k → ZMod N) : (t.run enc env).2 ≤ q := by
  induction t with
  | output => exact Nat.zero_le _
  | query op next ih => exact Nat.succ_le_succ (ih (enc (op.value env)) _)

/-- After fixing its own coins, the strategy takes two visible bit strings: the generator
label and the target label, in that order. It has no separate identity handle. -/
abbrev Strategy (N n q : ℕ) := (Fin n → Bool) → (Fin n → Bool) → Interaction N n 2 q

/-- The output for a fixed strategy, injection and secret. The hidden environment and the
visible inputs refer to the same two elements, even when `x = 1` and the labels coincide. -/
def observedOutput {N n q : ℕ} (a : Strategy N n q) (enc : Encoding N n) (x : ZMod N) : ZMod N :=
  ((a (enc 1) (enc x)).run enc ![1, x]).1

/-- Joint law of the secret and the observed output. The independently sampled coin value
selects a deterministic strategy. The encoding is uniform over *all* injections, and the
secret is independently uniform over the whole group of exponents. -/
noncomputable def experiment {N n q : ℕ} (hN : 1 < N) (hcap : N ≤ 2 ^ n) {R : Type*}
    (coins : PMF R) (a : R → Strategy N n q) : PMF (ZMod N × ZMod N) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI := encoding_nonempty hcap
  exact coins.bind fun r => (uniformOfFintype (Encoding N n)).bind fun enc =>
    (uniformOfFintype (ZMod N)).map fun x => (x, observedOutput (a r) enc x)

/-- If the output for each fixed coin value and encoding does not depend on the secret, the
chance of success is exactly `1/N`. The output need not be constant across encodings or coins. -/
theorem winProb_of_secret_independent {N n q : ℕ} (hN : 1 < N) (hcap : N ≤ 2 ^ n) {R : Type*}
    (coins : PMF R) (a : R → Strategy N n q) (y : R → Encoding N n → ZMod N)
    (hy : ∀ r enc x, observedOutput (a r) enc x = y r enc) :
    winProb ((experiment hN hcap coins a).map fun z => decide (z.2 = z.1)) = 1 / N := by
  have : NeZero N := ⟨by omega⟩
  have hmass (v : ZMod N) : ((uniformOfFintype (ZMod N)).map fun x => decide (v = x)) true =
      (N : ℝ≥0∞)⁻¹ := by
    rw [PMF.map_apply, tsum_eq_single v]
    · simp [ZMod.card]
    · intro x hx
      simp [Ne.symm hx]
  simp only [experiment, PMF.map_bind, PMF.map_comp, Function.comp_def, hy]
  simp only [winProb, PMF.bind_apply, hmass, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

end Cslib.Crypto.Framework.GenericGroup.RandomEncoding
