/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF

/-!
# Lamport one-time signatures: a forgery inverts the one-way function

Fix a function `f : X → Y` and a message length `ℓ`. A Lamport secret key is a family of
preimages `sk (i, b) : X` for each position `i < ℓ` and bit `b`; the public key is
`pk (i, b) = f (sk (i, b))`. The signature on `m : Fin ℓ → Bool` reveals `sk (i, m i)` for every
`i`, and `(m, σ)` verifies when `f (σ i) = pk (i, m i)` for every `i`.

* `verify_sign`: honest signatures verify.
* `forgeGame f A : PMF Bool` is the one-time existential forgery experiment: the secret key is
  uniform, the forger `A` (random coins in a finite type `R`) sees the public key, obtains one
  signature on a message of its choice, and wins with a valid signature on a different message.
* `invertGame f I : PMF Bool` is the one-wayness experiment: `x` is uniform, and the inverter `I`
  wins when it outputs a preimage of `f x`.
* `invert A` plants `f x` at a uniform position `(i, b)` of an otherwise honest public key, aborts
  if the forger asks to sign a message with `m i = b`, and otherwise returns `σ' i` from the
  forgery when `m' i = b`.
* `forgeGame_le` (**Lamport's scheme is one-time secure if `f` is one-way**, Katz and Lindell,
  Theorem 12.16): `Pr[A forges] ≤ 2 ℓ · Pr[invert A inverts f]` for `ℓ ≥ 1`, an exact finite
  inequality.

The games are `PMF Bool` experiments and the bound is an inequality between success
probabilities.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 12.6.1.
-/

@[expose] public section

namespace Cslib.Crypto.Signatures.Lamport

open Finset

variable {X Y : Type*} (f : X → Y) {ℓ : ℕ}

/-- **Lamport public key.** For a function $f : X \to Y$ and a secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$, the public key is the map
$pk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to Y$ with $pk(i, b) = f(sk(i, b))$. -/
def publicKey (sk : Fin ℓ × Bool → X) : Fin ℓ × Bool → Y := fun ib => f (sk ib)

/-- **Lamport signing.** The signature of a message $m \in \{0, 1\}^\ell$ under a secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ is $\sigma \in X^\ell$ with
$\sigma_i = sk(i, m_i)$ for every position $i < \ell$. -/
def sign (sk : Fin ℓ × Bool → X) (m : Fin ℓ → Bool) : Fin ℓ → X := fun i => sk (i, m i)

/-- **Lamport verification.** Let $f : X \to Y$. A signature $\sigma \in X^\ell$ on a message
$m \in \{0, 1\}^\ell$ is valid for a public key $pk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to Y$
when $f(\sigma_i) = pk(i, m_i)$ for every position $i < \ell$. -/
def Verify (pk : Fin ℓ × Bool → Y) (m : Fin ℓ → Bool) (σ : Fin ℓ → X) : Prop :=
  ∀ i, f (σ i) = pk (i, m i)

instance [DecidableEq Y] (pk : Fin ℓ × Bool → Y) (m : Fin ℓ → Bool) (σ : Fin ℓ → X) :
    Decidable (Verify f pk m σ) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- **Correctness of Lamport signatures.** Let $f : X \to Y$. For every secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ and every message $m \in \{0, 1\}^\ell$, the
Lamport signature of $m$ under $sk$ is valid for $m$ under the public key of $sk$. -/
theorem verify_sign (sk : Fin ℓ × Bool → X) (m : Fin ℓ → Bool) :
    Verify f (publicKey f sk) m (sign sk m) := fun _ => rfl

/-- **One-time forger.** A one-time forger for messages of length $\ell$, with random coins in a
set $R$, consists of two maps. The first takes a public key
$pk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to Y$ and coins $r \in R$ and returns the message
$m \in \{0, 1\}^\ell$ whose signature the forger requests. The second takes a public key, a
signature $\sigma \in X^\ell$ and coins $r$ and returns a message $m' \in \{0, 1\}^\ell$ together
with a signature $\sigma' \in X^\ell$. -/
structure Forger (X Y R : Type*) (ℓ : ℕ) where
  /-- The message whose signature the forger requests. -/
  choose : (Fin ℓ × Bool → Y) → R → Fin ℓ → Bool
  /-- The forgery. -/
  forge : (Fin ℓ × Bool → Y) → (Fin ℓ → X) → R → (Fin ℓ → Bool) × (Fin ℓ → X)

variable [Fintype X] [Nonempty X] [DecidableEq Y] {R : Type*} [Fintype R] [Nonempty R]

/-- **Winning the Lamport one-time forgery game.** Let $X$ be a nonempty finite set, $Y$ a set
with decidable equality, $f : X \to Y$ a function, and $\ell$ a message length; messages are bit
strings $m = (m_0, \dots, m_{\ell-1})$. A one-time forger $A$ with random coins from a nonempty
finite set $R$ wins against a secret key $sk$, which assigns $sk(i, b) \in X$ to each position
$i < \ell$ and bit $b$, with coins $r \in R$ when the following holds. Let $pk$ be the public key
of $sk$, given by $pk(i, b) = f(sk(i, b))$; let $m$ be the message that $A$ chooses from $pk$ and
$r$; and let $(m', \sigma')$ be the message and signature that $A$ outputs from $pk$, the
signature $i \mapsto sk(i, m_i)$ of $m$ under $sk$, and $r$. Then $m' \ne m$, and $\sigma'$ is a
valid signature on $m'$ for $pk$: $f(\sigma'_i) = pk(i, m'_i)$ for every $i < \ell$. -/
def Forger.Wins (A : Forger X Y R ℓ) (sk : Fin ℓ × Bool → X) (r : R) : Prop :=
  (A.forge (publicKey f sk) (sign sk (A.choose (publicKey f sk) r)) r).1 ≠
      A.choose (publicKey f sk) r ∧
    Verify f (publicKey f sk) (A.forge (publicKey f sk) (sign sk (A.choose (publicKey f sk) r)) r).1
      (A.forge (publicKey f sk) (sign sk (A.choose (publicKey f sk) r)) r).2

instance (A : Forger X Y R ℓ) (sk : Fin ℓ × Bool → X) (r : R) : Decidable (A.Wins f sk r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **One-time forgery game.** Let $f : X \to Y$ with $X$ finite and nonempty, and let $A$ be a
one-time forger for messages of length $\ell$ with random coins in a finite nonempty set $R$. The
one-time forgery game is the distribution on $\{\mathrm{true}, \mathrm{false}\}$ obtained by drawing
a secret key $sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ and coins $r \in R$ uniformly and
independently, and returning whether $A$ wins against $sk$ with coins $r$. -/
noncomputable def forgeGame (A : Forger X Y R ℓ) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((Fin ℓ × Bool → X) × R)).map fun ω =>
    decide (A.Wins f ω.1 ω.2)

/-- **One-wayness game.** Let $f : X \to Y$ with $X$ finite and nonempty, and let $I$ be an
inverter with random coins in a finite nonempty set $\Omega$: given $y \in Y$ and coins
$\omega \in \Omega$ it either outputs some $x' \in X$ or fails. The one-wayness game for $f$ is the
distribution on $\{\mathrm{true}, \mathrm{false}\}$ obtained by drawing $x \in X$ and
$\omega \in \Omega$ uniformly and independently and returning true exactly when $I$, run on $f(x)$
with coins $\omega$, outputs some $x'$ with $f(x') = f(x)$. -/
noncomputable def invertGame {Ω : Type*} [Fintype Ω] [Nonempty Ω] (I : Y → Ω → Option X) :
    PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (X × Ω)).map fun ω =>
    match I (f ω.1) ω.2 with
    | some x' => decide (f x' = f ω.1)
    | none => false

/-- **Planted public key.** Let $f : X \to Y$. Given a secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$, a position $(i, b)$ and a value $y \in Y$, the
planted public key takes the value $y$ at $(i, b)$ and the value $f(sk(j, c))$ at every other
position $(j, c)$. -/
def plant (sk : Fin ℓ × Bool → X) (ib : Fin ℓ × Bool) (y : Y) : Fin ℓ × Bool → Y :=
  fun jc => if jc = ib then y else f (sk jc)

/-- **Inverter built from a forger.** Let $f : X \to Y$, let $A$ be a one-time forger for messages
of length $\ell$ with coins in $R$, and let $y \in Y$. The inverter's coins are a position $(i, b)$
with $i < \ell$ and $b \in \{0, 1\}$, a secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ and forger coins $r \in R$. It forms the
public key $pk$ with $pk(i, b) = y$ and $pk(j, c) = f(sk(j, c))$ for every other $(j, c)$, and
runs $A$ on $pk$ with coins $r$ to obtain the message $m$ whose signature $A$ requests. If
$m_i = b$ it fails. Otherwise it hands $A$ the signature $(sk(j, m_j))_{j < \ell}$ of $m$ under
$sk$ and obtains a forgery $(m', \sigma')$; it outputs $\sigma'_i$ if $m'_i = b$ and fails
otherwise. -/
def invert (A : Forger X Y R ℓ) (y : Y) (ω : (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R) :
    Option X :=
  if A.choose (plant f ω.2.1 ω.1 y) ω.2.2 ω.1.1 = ω.1.2 then none
  else if (A.forge (plant f ω.2.1 ω.1 y) (sign ω.2.1 (A.choose (plant f ω.2.1 ω.1 y) ω.2.2))
      ω.2.2).1 ω.1.1 = ω.1.2 then
    some ((A.forge (plant f ω.2.1 ω.1 y) (sign ω.2.1 (A.choose (plant f ω.2.1 ω.1 y) ω.2.2))
      ω.2.2).2 ω.1.1)
  else none

omit [Fintype X] [Nonempty X] [DecidableEq Y] in
private theorem map_uniform_toReal {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → Bool) :
    ((Cslib.Probability.PMF.uniformOfFintype Ω).map g true).toReal =
      (∑ ω, if g ω = true then (1 : ℝ) else 0) / Fintype.card Ω := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun ω _ => by split_ifs <;> simp)]
  rw [div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hg : g ω = true <;> simp [hg, eq_comm (a := true)]

/-- The inverter's success indicator. -/
private def invWin (A : Forger X Y R ℓ) (x : X) (ω : (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R) :
    ℝ :=
  match invert f A (f x) ω with
  | some x' => if f x' = f x then 1 else 0
  | none => 0

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
private theorem plant_update (sk : Fin ℓ × Bool → X) (ib : Fin ℓ × Bool) (x : X) (y : Y) :
    plant f (Function.update sk ib x) ib y = plant f sk ib y := by
  funext jc
  by_cases h : jc = ib <;> simp [plant, h]

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
private theorem sign_update {sk : Fin ℓ × Bool → X} {ib : Fin ℓ × Bool} {m : Fin ℓ → Bool}
    (hm : m ib.1 ≠ ib.2) (x : X) : sign (Function.update sk ib x) m = sign sk m := by
  funext j
  refine Function.update_of_ne (fun h => hm ?_) _ _
  rw [← h]

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
/-- The inverter never reads the secret-key entry at the planted position. -/
private theorem invert_update (A : Forger X Y R ℓ) (y : Y) (ib : Fin ℓ × Bool)
    (sk : Fin ℓ × Bool → X) (r : R) (x : X) :
    invert f A y (ib, Function.update sk ib x, r) = invert f A y (ib, sk, r) := by
  by_cases h1 : A.choose (plant f sk ib y) r ib.1 = ib.2
  · simp only [invert, plant_update, h1, ↓reduceIte]
  · simp only [invert, plant_update, h1, ↓reduceIte, sign_update h1]

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
/-- Planting `f (sk ib)` at `ib` gives the honest public key. -/
private theorem plant_self (sk : Fin ℓ × Bool → X) (ib : Fin ℓ × Bool) :
    plant f sk ib (f (sk ib)) = publicKey f sk := by
  funext jc
  by_cases h : jc = ib <;> simp [plant, publicKey, h]

omit [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- If the forger wins against `sk`, the inverter run on the honest key with the guess
`(j, m' j)` at a position where the messages differ succeeds. -/
private theorem one_le_sum_invWin (A : Forger X Y R ℓ) (sk : Fin ℓ × Bool → X) (r : R)
    (hw : A.Wins f sk r) : 1 ≤ ∑ ib : Fin ℓ × Bool, invWin f A (sk ib) (ib, sk, r) := by
  obtain ⟨hne, hver⟩ := hw
  set m := A.choose (publicKey f sk) r
  set out := A.forge (publicKey f sk) (sign sk m) r
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hnonneg : ∀ ib, 0 ≤ invWin f A (sk ib) (ib, sk, r) := by
    intro ib
    simp only [invWin]
    split <;> [split_ifs <;> norm_num; exact le_rfl]
  have hone : invWin f A (sk (j, out.1 j)) ((j, out.1 j), sk, r) = 1 := by
    simp only [invWin, invert, plant_self]
    have h1 : ¬ A.choose (publicKey f sk) r j = out.1 j := fun h => hj h.symm
    simp only [h1, ↓reduceIte]
    change (match (if out.1 j = out.1 j then some (out.2 j) else none) with
      | some x' => if f x' = f (sk (j, out.1 j)) then (1 : ℝ) else 0 | none => 0) = 1
    simp only [↓reduceIte]
    simp only [show f (out.2 j) = f (sk (j, out.1 j)) from hver j, ↓reduceIte]
  calc (1 : ℝ) = invWin f A (sk (j, out.1 j)) ((j, out.1 j), sk, r) := hone.symm
    _ ≤ _ := single_le_sum (fun ib _ => hnonneg ib) (mem_univ _)

omit [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
/-- Re-randomizing one secret-key entry: `∑ x, ∑ sk, G (update sk ib x) = |X| · ∑ sk, G sk`. -/
private theorem sum_sum_update [DecidableEq (Fin ℓ × Bool)] (ib : Fin ℓ × Bool)
    (G : (Fin ℓ × Bool → X) → ℝ) :
    ∑ x : X, ∑ sk : Fin ℓ × Bool → X, G (Function.update sk ib x) =
      Fintype.card X * ∑ sk, G sk := by
  have hR : (Fintype.card X : ℝ) * ∑ sk, G sk = ∑ q : (Fin ℓ × Bool → X) × X, G q.1 := by
    rw [Fintype.sum_prod_type, mul_sum]
    simp [sum_const, Finset.card_univ]
  let e : X × (Fin ℓ × Bool → X) ≃ (Fin ℓ × Bool → X) × X :=
    { toFun := fun p => (Function.update p.2 ib p.1, p.2 ib)
      invFun := fun q => (q.1 ib, Function.update q.1 ib q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  rw [hR, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ fun p => rfl

/-- **Security reduction for Lamport one-time signatures.** Let $f : X \to Y$ be a function on a
finite nonempty set $X$, let $\ell \ge 1$ be the message length, and let $A$ be a one-time forger
whose random coins range over a finite nonempty set $R$. Then the probability that $A$ wins the
one-time forgery game against the Lamport scheme built from $f$ is at most $2\ell$ times the
probability that the inverter built from $A$ wins the one-wayness game for $f$.

This is the reduction behind Katz and Lindell, Theorem 12.16: if $f$ is one-way, then Lamport's
scheme is one-time secure. -/
theorem forgeGame_le [NeZero ℓ] (A : Forger X Y R ℓ) :
    (forgeGame f A true).toReal ≤ 2 * ℓ * (invertGame f (invert f A) true).toReal := by
  classical
  rw [forgeGame, invertGame, map_uniform_toReal, map_uniform_toReal]
  have hcard : Fintype.card (X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R) =
      Fintype.card X * (2 * ℓ) * Fintype.card ((Fin ℓ × Bool → X) × R) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hΩ : (0 : ℝ) < Fintype.card ((Fin ℓ × Bool → X) × R) := by exact_mod_cast Fintype.card_pos
  -- the inverter's success sum, as a sum of `invWin`
  have hinv : (∑ ω : X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R,
      if (match invert f A (f ω.1) ω.2 with
        | some x' => decide (f x' = f ω.1)
        | none => false) = true then (1 : ℝ) else 0) =
      ∑ ω : X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R, invWin f A ω.1 ω.2 := by
    refine sum_congr rfl fun ω _ => ?_
    simp only [invWin]
    split <;> simp
  -- re-randomize the planted entry
  have hsum : ∑ ω : X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R, invWin f A ω.1 ω.2 =
      Fintype.card X * ∑ ib : Fin ℓ × Bool, ∑ sk : Fin ℓ × Bool → X, ∑ r : R,
        invWin f A (sk ib) (ib, sk, r) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type (α₁ := Fin ℓ × Bool) (α₂ := (Fin ℓ × Bool → X) × R),
      Fintype.sum_prod_type (α₁ := Fin ℓ × Bool → X) (α₂ := R)]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun ib _ => ?_
    rw [← sum_sum_update ib (fun sk => ∑ r : R, invWin f A (sk ib) (ib, sk, r))]
    refine sum_congr rfl fun x _ => sum_congr rfl fun sk _ => sum_congr rfl fun r _ => ?_
    simp only [invWin, Function.update_self, invert_update]
  -- each winning `(sk, r)` contributes at least one successful guess
  have hwin : (∑ ω : (Fin ℓ × Bool → X) × R, if decide (A.Wins f ω.1 ω.2) = true then (1 : ℝ)
      else 0) ≤ ∑ ib : Fin ℓ × Bool, ∑ sk : Fin ℓ × Bool → X, ∑ r : R,
        invWin f A (sk ib) (ib, sk, r) := by
    have hswap : (∑ ib : Fin ℓ × Bool, ∑ sk : Fin ℓ × Bool → X, ∑ r : R,
        invWin f A (sk ib) (ib, sk, r)) =
        ∑ sk : Fin ℓ × Bool → X, ∑ r : R, ∑ ib : Fin ℓ × Bool, invWin f A (sk ib) (ib, sk, r) := by
      rw [sum_comm]
      exact sum_congr rfl fun sk _ => sum_comm
    rw [hswap, Fintype.sum_prod_type (α₁ := Fin ℓ × Bool → X) (α₂ := R)]
    refine sum_le_sum fun sk _ => sum_le_sum fun r _ => ?_
    by_cases hw : A.Wins f sk r
    · simp only [hw, decide_true, ↓reduceIte]
      exact one_le_sum_invWin f A sk r hw
    · simp only [hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine sum_nonneg fun ib _ => ?_
      simp only [invWin]
      split <;> [split_ifs <;> norm_num; exact le_rfl]
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  rw [hinv, hsum, hcard, div_le_iff₀ hΩ]
  push_cast
  rw [show ∀ S : ℝ, 2 * ℓ * ((Fintype.card X * S) /
      (Fintype.card X * (2 * ℓ) * Fintype.card ((Fin ℓ × Bool → X) × R))) *
      Fintype.card ((Fin ℓ × Bool → X) × R) = S from fun S => by field_simp]
  exact hwin

end Cslib.Crypto.Signatures.Lamport
