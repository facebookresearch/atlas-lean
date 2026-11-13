/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.Modes

/-!
# CBC-MAC

The basic CBC-MAC of Katz and Lindell (Construction 4.11) authenticates a message of `ℓ` blocks
with a block cipher `F`: `t₀ = 0`, `tᵢ = F_k (tᵢ₋₁ + mᵢ)`, and the tag is `t_ℓ`, the last block of
CBC encryption with the all-zero initial vector (`cbcMacFrom_succ_eq_cbcChain`).

* `cbcMac`, `cbcMacScheme ℓ E`: fixed-length CBC-MAC as a framework `MACScheme`, and
  `cbcMacScheme_correct`.
* `cbcMacList`, `cbcMacVarScheme E`: the same chaining applied to messages of any length.
  `macAdvantage_lengthExtForger`: **for every block cipher**, the forger that asks for the tag `t`
  of a one-block message `x` and outputs the two-block message `[x, x - t]` with the same tag `t`
  wins with probability `1`. So basic CBC-MAC is insecure for variable-length messages, which is
  why Katz and Lindell's Theorem 4.12 is stated for fixed-length messages.

**Deferred.** The EUF-CMA security of fixed-length CBC-MAC from PRP security (Katz and Lindell,
Theorem 4.12) and the length-prefixed / encrypted (EMAC) variable-length extensions are not proved
here. The step from a uniformly random permutation to a uniformly random function is the switching
lemma `Cslib.Crypto.Framework.LazySampling.switching_lemma`; what both still need is the
collision analysis of CBC chaining against a random function (collisions among adaptively chosen
chaining inputs), which this file does not develop (see the deferred note of
`CSLibExt.Crypto.SymmetricKey.Modes`).

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 4.4.1 (Construction 4.11, Theorem 4.12).
-/

@[expose] public section

namespace Cslib.Crypto.Modes

open Cslib.Crypto.Framework Cslib.Crypto.Framework.OracleComp

variable {X : Type*} [AddCommGroup X]

/-- The CBC-MAC chaining from the value `acc`: `tᵢ = p (tᵢ₋₁ + mᵢ)`, returning the last value. -/
def cbcMacFrom (p : X → X) (acc : X) : (n : ℕ) → (Fin n → X) → X
  | 0, _ => acc
  | n + 1, m => cbcMacFrom p (p (acc + m 0)) n (Fin.tail m)

/-- On a nonempty message, the CBC-MAC chaining ends at the last block of the CBC chain. -/
theorem cbcMacFrom_succ_eq_cbcChain (p : X → X) :
    ∀ (n : ℕ) (acc : X) (m : Fin (n + 1) → X),
      cbcMacFrom p acc (n + 1) m = cbcChain p acc (n + 1) m (Fin.last n)
  | 0, _, _ => rfl
  | n + 1, acc, m => by
    rw [cbcMacFrom, cbcMacFrom_succ_eq_cbcChain p n]
    change _ = Fin.cons (α := fun _ => X) (p (acc + m 0))
      (cbcChain p (p (acc + m 0)) (n + 1) (Fin.tail m)) (Fin.last (n + 1))
    rw [← Fin.succ_last, Fin.cons_succ]

variable {ℓ : ℕ}

/-- **Basic CBC-MAC** (Katz and Lindell, Construction 4.11) of an `ℓ`-block message: CBC chaining
with the all-zero initial vector, keeping only the last block. -/
def cbcMac (p : X → X) (m : Fin ℓ → X) : X := cbcMacFrom p 0 ℓ m

variable {K : Type*} [Fintype K] [Nonempty K] [DecidableEq X]

variable (ℓ) in
/-- **Fixed-length CBC-MAC** from a block cipher `E` (Katz and Lindell, Construction 4.11): a
uniform key; the tag is deterministic and verification recomputes it. -/
noncomputable def cbcMacScheme (E : BlockCipher K X) : MACScheme (Fin ℓ → X) K X where
  gen := Cslib.Probability.PMF.uniformOfFintype K
  tag k m := PMF.pure (cbcMac (E k) m)
  verify k m t := decide (cbcMac (E k) m = t)

/-- **Correctness** of fixed-length CBC-MAC. -/
theorem cbcMacScheme_correct (E : BlockCipher K X) : (cbcMacScheme ℓ E).Correct := by
  intro k _ m t ht
  simp only [cbcMacScheme, PMF.support_pure, Set.mem_singleton_iff] at ht
  simp [cbcMacScheme, ht]

/-- CBC-MAC chaining applied to a message of any number of blocks. -/
def cbcMacList (p : X → X) (m : List X) : X := m.foldl (fun acc x => p (acc + x)) 0

/-- Basic CBC-MAC used for messages of variable length (insecure:
`macAdvantage_lengthExtForger`). -/
noncomputable def cbcMacVarScheme (E : BlockCipher K X) : MACScheme (List X) K X where
  gen := Cslib.Probability.PMF.uniformOfFintype K
  tag k m := PMF.pure (cbcMacList (E k) m)
  verify k m t := decide (cbcMacList (E k) m = t)

omit [DecidableEq X] in
/-- The length-extension forger: ask for the tag `t` of the one-block message `[x]` and output the
two-block message `[x, x - t]` with the tag `t`. -/
noncomputable def lengthExtForger (x : X) : MACForger (List X) X Unit where
  coins := PMF.pure ()
  forge _ := .liftBind [x] fun t => .pure ([x, x - t], t)

omit [DecidableEq X] in
/-- The length-extension forger makes one query. -/
theorem lengthExtForger_queryBounded (x : X) : (lengthExtForger x).QueryBounded 1 :=
  fun _ _ => trivial

/-- **Basic CBC-MAC is insecure for variable-length messages** (Katz and Lindell, Section 4.4.1):
against every block cipher, the length-extension forger, with one query, forges with
probability `1`: the tag of `[x, x - t]` is `F_k (F_k x + x - t) = F_k x = t`. -/
theorem macAdvantage_lengthExtForger (E : BlockCipher K X) (x : X) :
    macAdvantage (cbcMacVarScheme E) (lengthExtForger x) = 1 := by
  have h : macGame (cbcMacVarScheme E) (lengthExtForger x) = PMF.pure true := by
    simp only [macGame, cbcMacVarScheme, lengthExtForger, evalLog, PMF.pure_bind, PMF.pure_map]
    simp [cbcMacList]
  rw [macAdvantage, h, winProb_pure]
  rfl

end Cslib.Crypto.Modes
