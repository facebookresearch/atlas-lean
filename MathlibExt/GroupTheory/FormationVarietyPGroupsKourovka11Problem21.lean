/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Group.Commutator
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Formations of finite p-groups cut out by varieties (Kourovka Notebook Problem 11.21)

Kourovka Notebook, Archive of Solved Problems, Problem 11.21 (A. F. Vasil'yev): let `𝔑_p` be the
formation of all finite `p`-groups. Is every subformation `𝔉` of `𝔑_p` of the form `𝔑_p ∩ 𝔐` for a
variety `𝔐`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.21 (A. F.
Vasil'yev). UnsolvedMath record UM-00700714 (`KOU-11.21`), dataset ulamai/UnsolvedMath v1.8.0.

A class of groups is a predicate on groups in `Type`. A formation is a nonempty, isomorphism-closed
class of finite groups closed under quotients and subdirect products (`G / M, G / N ∈ 𝔉` implies `G
/ (M ∩ N) ∈ 𝔉`); nonemptiness excludes the empty class, which no variety cuts out (every variety
contains the trivial `p`-group). A variety is the class of groups satisfying a set `W` of laws,
words in the free group on countably many letters. `𝔉 = 𝔑_p ∩ 𝔐` means that a finite `p`-group lies
in `𝔉` iff it satisfies `W`. The prime `p` is universally quantified, so the refutation asserts a
counterexample for some prime.

The theorem `subformationOfPGroupsIsVarietal_refuted` gives a counterexample at the prime 3.

## Proof

Take the Heisenberg group over ℤ[X, 1/(4X)] and extend it by a cyclic diagonal group. The diagonal
generator acts on the two coordinates of the abelianization with weights 4 and X/4, and on the
central coordinate with weight X.
A commutator word tests whether the sum of the two weights agrees with the sum of the powers
Xʳ and X¹⁻ʳ. The word is evaluated on commutators so that its inputs lie in the Heisenberg group.

Embed the coefficient ring in the 3-adic integers by sending X to a transcendental element
congruent to 4 modulo 9. At each finite level choose an exponent r for which Xʳ = 4. The finite
3-groups satisfying all sufficiently late test words form a formation containing these reductions.
Any ordinary law shared by the reductions holds in the generic group because they separate its
elements. It then holds in the quotient obtained by setting X = 1 modulo 243. That quotient
fails every test word.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted

/-- **Classes of groups.** A class of groups is a predicate on groups: it assigns to every group
$G$ (in the lowest universe of types) a proposition, read as "$G$ belongs to the class". No
closure under isomorphism is required. -/
abbrev GroupClass : Type 1 := ∀ (G : Type) [Group G], Prop

/-- **Formations of finite groups.** A class $\mathfrak F$ of groups is a formation when every group
in $\mathfrak F$ is finite, $\mathfrak F$ contains at least one group, $\mathfrak F$ is closed under
isomorphism, $\mathfrak F$ is closed under quotients (if $G \in \mathfrak F$ and $N$ is a normal
subgroup of $G$, then $G/N \in \mathfrak F$), and $\mathfrak F$ is closed under subdirect products:
if $G$ is a finite group with normal subgroups $M$ and $N$ such that $G/M \in \mathfrak F$ and
$G/N \in \mathfrak F$, then $G/(M \cap N) \in \mathfrak F$. -/
structure IsFormation (F : GroupClass) : Prop where
  finite : ∀ (G : Type) [Group G], F G → Finite G
  nonempty : ∃ (G : Type) (_ : Group G), F G
  of_mulEquiv : ∀ (G H : Type) [Group G] [Group H], (G ≃* H) → F G → F H
  quotient : ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], F G → F (G ⧸ N)
  subdirect : ∀ (G : Type) [Group G] [Finite G] (M N : Subgroup G) [M.Normal] [N.Normal],
    F (G ⧸ M) → F (G ⧸ N) → F (G ⧸ (M ⊓ N))

/-- **Groups satisfying a set of laws.** Let $W$ be a set of words in the free group on countably
many generators $x_0, x_1, x_2, \dots$. A group $G$ satisfies the laws in $W$ when every
homomorphism from this free group to $G$ sends every $w \in W$ to $1$. The groups satisfying $W$
form the variety defined by $W$, and every variety arises this way. -/
def SatisfiesLaws (W : Set (FreeGroup ℕ)) (G : Type) [Group G] : Prop :=
  ∀ w ∈ W, ∀ f : FreeGroup ℕ →* G, f w = 1

/-- **Kourovka Problem 11.21 (Vasil'yev's question on formations of $p$-groups).** The proposition
that for every prime $p$ and every formation $\mathfrak F$ all of whose members are $p$-groups (a
subformation of the formation $\mathfrak N_p$ of all finite $p$-groups), there is a set $W$ of laws,
words in the free group on countably many generators, such that a finite $p$-group lies in
$\mathfrak F$ if and only if it satisfies every law in $W$. In other words, every such
$\mathfrak F$ equals $\mathfrak N_p \cap \mathfrak M$ for the variety $\mathfrak M$ defined by
$W$. -/
def subformationOfPGroupsIsVarietal : Prop :=
  ∀ p : ℕ, p.Prime → ∀ F : GroupClass, IsFormation F →
    (∀ (G : Type) [Group G], F G → IsPGroup p G) →
    ∃ W : Set (FreeGroup ℕ), ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
      (F G ↔ SatisfiesLaws W G)

noncomputable section

open scoped commutatorElement

-- The cyclic diagonal acts on the Heisenberg coordinates by (x, y, z) ↦ (ax, by, abz).
private abbrev Diagonal {R : Type} [CommRing R] (a b : Rˣ) := Subgroup.zpowers (a, b)

@[ext] private structure Triangular {R : Type} [CommRing R] (a b : Rˣ) where
  t : Diagonal a b
  x : R
  y : R
  z : R

variable {R S : Type} [CommRing R] [CommRing S] {a b : Rˣ}

private abbrev weight₁ (t : Diagonal a b) : Rˣ := t.val.1
private abbrev weight₂ (t : Diagonal a b) : Rˣ := t.val.2

private def triangularMul (g h : Triangular a b) : Triangular a b :=
  ⟨g.t * h.t, g.x + weight₁ g.t * h.x, g.y + weight₂ g.t * h.y,
    g.z + weight₁ g.t * weight₂ g.t * h.z + g.x * weight₂ g.t * h.y⟩

private def triangularInv (g : Triangular a b) : Triangular a b :=
  ⟨g.t⁻¹, -((weight₁ g.t)⁻¹ : Rˣ) * g.x, -((weight₂ g.t)⁻¹ : Rˣ) * g.y,
    ((weight₁ g.t)⁻¹ : Rˣ) * ((weight₂ g.t)⁻¹ : Rˣ) * (g.x * g.y - g.z)⟩

private def triangularOne : Triangular a b := ⟨1, 0, 0, 0⟩

private instance triGroup : Group (Triangular a b) where
  one := triangularOne
  mul := triangularMul
  inv := triangularInv
  mul_assoc g h k := by
    change triangularMul (triangularMul g h) k = triangularMul g (triangularMul h k)
    ext1 <;> simp [triangularMul, weight₁, weight₂, mul_assoc] <;> ring
  one_mul g := by
    change triangularMul triangularOne g = g
    ext1 <;> simp [triangularMul, triangularOne, weight₁, weight₂]
  mul_one g := by
    change triangularMul g triangularOne = g
    ext1 <;> simp [triangularMul, triangularOne, weight₁, weight₂]
  inv_mul_cancel g := by
    change triangularMul (triangularInv g) g = triangularOne
    ext1 <;> simp [triangularMul, triangularInv, triangularOne, weight₁, weight₂]
    ring

private def diagonalPart : Triangular a b →* Diagonal a b where
  toFun := Triangular.t
  map_one' := rfl
  map_mul' _ _ := rfl

private def unipotent (x y z : R) : Triangular a b := ⟨1, x, y, z⟩

private def diagonalGenerator (a b : Rˣ) : Triangular a b :=
  ⟨⟨(a, b), Subgroup.mem_zpowers _⟩, 0, 0, 0⟩

private theorem diagonalPart_comm (g h : Triangular a b) : ⁅g, h⁆.t = 1 := by
  change diagonalPart ⁅g, h⁆ = 1
  simp [commutatorElement_def, mul_assoc]

private theorem eq_unipotent (g : Triangular a b) (h : g.t = 1) : g = unipotent g.x g.y g.z := by
  ext1 <;> first | exact h | rfl

private theorem comm_unipotent (x y z u v w : R) :
    ⁅(unipotent x y z : Triangular a b), (unipotent u v w : Triangular a b)⁆ =
      unipotent 0 0 (x * v - u * y) := by
  change triangularMul (triangularMul (triangularMul _ _) (triangularInv _)) (triangularInv _) = _
  ext1 <;> simp [triangularMul, triangularInv, unipotent, weight₁, weight₂]
  ring

private theorem conjugate_unipotent (g : Triangular a b) (x y z : R) :
    MulAut.conj g (unipotent x y z) =
      unipotent (weight₁ g.t * x) (weight₂ g.t * y)
        (weight₁ g.t * weight₂ g.t * z + g.x * weight₂ g.t * y - g.y * weight₁ g.t * x) := by
  change triangularMul (triangularMul g _) (triangularInv g) = _
  have ha : (weight₁ g.t : R) * (↑((weight₁ g.t)⁻¹) : R) = 1 := (weight₁ g.t).val_inv
  have hb : (weight₂ g.t : R) * (↑((weight₂ g.t)⁻¹) : R) = 1 := (weight₂ g.t).val_inv
  ext1 <;> simp [triangularMul, triangularInv, unipotent, weight₁, weight₂]
  grind

-- For commutators u, v in the unipotent subgroup, the two factors on the left
-- multiply their determinant by the trace of t. On the right, conjugation on
-- the center scales by powers of its determinant.
private def discrepancy {G : Type} [Group G] (r : ℤ) (t u v : G) : G :=
  (⁅MulAut.conj t u, v⁆ * ⁅u, MulAut.conj t v⁆) *
    (MulAut.conj (t ^ r) ⁅u, v⁆ * MulAut.conj (t ^ (1 - r)) ⁅u, v⁆)⁻¹

private def testWord (r : ℤ) : FreeGroup ℕ :=
  discrepancy r (.of 0) ⁅FreeGroup.of 1, FreeGroup.of 2⁆ ⁅FreeGroup.of 3, FreeGroup.of 4⁆

private theorem eval_testWord {G : Type} [Group G] (r : ℤ) (f : FreeGroup ℕ →* G) :
    f (testWord r) = discrepancy r (f (.of 0)) ⁅f (.of 1), f (.of 2)⁆ ⁅f (.of 3), f (.of 4)⁆ := by
  simp only [testWord, discrepancy, commutatorElement_def, MulAut.conj_apply]
  simp only [map_mul, map_inv, map_zpow]

private theorem discrepancy_unipotent (r : ℤ) (g : Triangular a b) (x y z u v w : R) :
    discrepancy r g (unipotent x y z) (unipotent u v w) =
      unipotent 0 0 (((weight₁ g.t : R) + weight₂ g.t -
        (↑((weight₁ g.t * weight₂ g.t) ^ r) : R) -
        ↑((weight₁ g.t * weight₂ g.t) ^ (1 - r))) * (x * v - u * y)) := by
  have h (n : ℤ) : (g ^ n).t = g.t ^ n := map_zpow diagonalPart g n
  simp only [discrepancy, conjugate_unipotent, comm_unipotent, h]
  change triangularMul (triangularMul _ _) (triangularInv (triangularMul _ _)) = _
  ext1 <;> simp [triangularMul, triangularInv, unipotent, weight₁, weight₂, mul_zpow]
  ring

private theorem testWord_eq_one (r : ℤ) (h : (a * b) ^ r = a) (f : FreeGroup ℕ →* Triangular a b) :
    f (testWord r) = 1 := by
  let t := f (.of 0)
  let u := ⁅f (.of 1), f (.of 2)⁆
  let v := ⁅f (.of 3), f (.of 4)⁆
  have e : f (testWord r) = discrepancy r t u v := eval_testWord r f
  rw [e, eq_unipotent u (diagonalPart_comm ..), eq_unipotent v (diagonalPart_comm ..),
    discrepancy_unipotent]
  obtain ⟨k, hk⟩ := t.t.property
  have ha : weight₁ t.t = a ^ k := congrArg Prod.fst hk.symm
  have hb : weight₂ t.t = b ^ k := congrArg Prod.snd hk.symm
  have h' : (a * b) ^ (1 - r) = b := by rw [zpow_sub, zpow_one, h]; simp
  have powers (j : ℤ) : (a ^ k * b ^ k) ^ j = ((a * b) ^ j) ^ k := by
    rw [← mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm k j]
  simp [ha, hb, powers, h, h', unipotent]
  rfl

private theorem tri_mul (g h : Triangular a b) : g * h = triangularMul g h := rfl

private theorem tri_one : (1 : Triangular a b) = triangularOne := rfl

private def triMap {c d : Sˣ} (f : R →+* S)
    (ha : Units.map f a = c) (hb : Units.map f b = d) : Triangular a b →* Triangular c d where
  toFun g :=
    { t := ⟨(Units.map f (weight₁ g.t), Units.map f (weight₂ g.t)), by
        obtain ⟨n, hn⟩ := g.t.property
        use n
        change (c ^ n, d ^ n) = _
        rw [← ha, ← hb, ← map_zpow, ← map_zpow]
        congr 1 <;> apply congrArg
        · exact congrArg Prod.fst hn
        · exact congrArg Prod.snd hn⟩
      x := f g.x, y := f g.y, z := f g.z }
  map_mul' g h := by
    ext1
    · apply Subtype.ext
      ext1 <;> simp [tri_mul, triangularMul, weight₁, weight₂]
    all_goals simp [tri_mul, triangularMul, weight₁, weight₂]
  map_one' := by ext1 <;> simp [tri_one, triangularOne, weight₁, weight₂]

private def triEquiv (a b : Rˣ) : Triangular a b ≃ Diagonal a b × R × R × R where
  toFun g := (g.t, g.x, g.y, g.z)
  invFun g := ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance triFinite [Finite R] : Finite (Triangular a b) := .of_equiv _ (triEquiv a b).symm

private theorem triPGroup {n : ℕ} {a b : (ZMod (3 ^ n))ˣ} {k : ℕ}
    (ha : a ^ 3 ^ k = 1) (hb : b ^ 3 ^ k = 1) : IsPGroup 3 (Triangular a b) := by
  have ht : orderOf (a, b) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (Prod.ext ha hb)
  apply IsPGroup.of_card_dvd_pow (n := k + n + n + n)
  rw [Nat.card_congr (triEquiv a b)]
  simpa [Nat.card_prod, Nat.card_zmod, Diagonal, Fintype.card_zpowers, pow_add, mul_assoc] using
    Nat.mul_dvd_mul_right ht (3 ^ n * (3 ^ n * 3 ^ n))

private theorem triMap_surjective {c d : Sˣ} (f : R →+* S) (hf : Function.Surjective f)
    (ha : Units.map f a = c) (hb : Units.map f b = d) :
    Function.Surjective (triMap f ha hb) := by
  rintro ⟨⟨_, n, rfl⟩, x, y, z⟩
  obtain ⟨x, rfl⟩ := hf x
  obtain ⟨y, rfl⟩ := hf y
  obtain ⟨z, rfl⟩ := hf z
  refine ⟨⟨⟨(a, b) ^ n, n, rfl⟩, x, y, z⟩, ?_⟩
  ext1
  · apply Subtype.ext
    ext1 <;> simp [triMap, weight₁, weight₂, ha, hb]
  all_goals rfl

-- At determinant 1 the right-hand factor loses all dependence on the exponent.
-- The weights 4 and 1/4 give a nonzero discrepancy modulo 243.
private abbrev M := ZMod (3 ^ 5)
private def four : Mˣ := ⟨4, 61, by decide, by decide⟩

private theorem specialization_fails (r : ℤ) :
    ∃ f : FreeGroup ℕ →* Triangular four four⁻¹, f (testWord r) ≠ 1 := by
  let t := diagonalGenerator four four⁻¹
  let x : Triangular four four⁻¹ := unipotent 1 0 0
  let y : Triangular four four⁻¹ := unipotent 0 1 0
  let f := FreeGroup.lift (fun | 0 | 1 | 3 => t | 2 => x | _ => y)
  refine ⟨f, ?_⟩
  have hf : f (testWord r) = discrepancy r t ⁅t, x⁆ ⁅t, y⁆ := by
    exact eval_testWord r f
  rw [hf, eq_unipotent ⁅t, x⁆ (diagonalPart_comm ..), eq_unipotent ⁅t, y⁆ (diagonalPart_comm ..),
    discrepancy_unipotent]
  intro h
  have hz := congrArg Triangular.z h
  change ((↑four + ↑four⁻¹ - (↑((four * four⁻¹) ^ r) : M) -
    ↑((four * four⁻¹) ^ (1 - r))) *
    (⁅t, x⁆.x * ⁅t, y⁆.y - ⁅t, y⁆.x * ⁅t, x⁆.y)) = 0 at hz
  simp only [mul_inv_cancel, one_zpow, Units.val_one] at hz
  have value : (↑four + ↑four⁻¹ - 1 - 1 : M) *
      (⁅t, x⁆.x * ⁅t, y⁆.y - ⁅t, y⁆.x * ⁅t, x⁆.y) = 162 := by decide
  exact (by decide : (162 : M) ≠ 0) (value.symm.trans hz)

open Polynomial

private theorem coefficient_choice : ∃ v : ℤ_[3], Transcendental ℤ (4 + 9 * v) := by
  have hd := (Algebraic.countable ℤ ℚ_[3]).dense_compl ℚ_[3]
  obtain ⟨q, ht, hq⟩ := hd.exists_mem_open (U := Metric.ball (4 : ℚ_[3]) ‖(9 : ℚ_[3])‖)
    Metric.isOpen_ball ⟨4, Metric.mem_ball_self (norm_pos_iff.mpr (by norm_num))⟩
  have h9 : (9 : ℚ_[3]) ≠ 0 := by norm_num
  let v : ℤ_[3] := ⟨(q - 4) / 9, by
    change ‖(q - 4) / 9‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr h9)]
    exact (show dist q 4 < ‖(9 : ℚ_[3])‖ from hq).le⟩
  use v
  intro h
  apply ht
  have he : ((4 + 9 * v : ℤ_[3]) : ℚ_[3]) = q := by
    change 4 + 9 * ((q - 4) / 9) = q
    field_simp
    ring
  rw [← he]
  exact h.algHom (IsScalarTower.toAlgHom ℤ ℤ_[3] ℚ_[3])

-- Inverting 4X makes both diagonal weights, 4 and X/4, units.
private abbrev denominator : ℤ[X] := 4 * X
private abbrev CoeffRing := Localization.Away denominator

private def alpha : CoeffRingˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := CoeffRing) denominator (dvd_mul_right 4 X)).unit

private def delta : CoeffRingˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := CoeffRing) denominator (dvd_mul_left X 4)).unit

private def beta : CoeffRingˣ := delta / alpha

private def specialize {S : Type} [CommRing S] (s : S) (h : IsUnit (4 * s)) : CoeffRing →+* S :=
  IsLocalization.Away.lift denominator (g := (aeval s : ℤ[X] →ₐ[ℤ] S).toRingHom)
    (by simpa [denominator, map_ofNat] using h)

private theorem spec_alpha {S : Type} [CommRing S] (s : S) (h : IsUnit (4 * s)) :
    specialize s h (alpha : CoeffRing) = 4 := by simp [specialize, alpha, map_ofNat]

private theorem spec_delta {S : Type} [CommRing S] (s : S) (h : IsUnit (4 * s)) :
    specialize s h (delta : CoeffRing) = s := by simp [specialize, delta]

private theorem spec_inj {S : Type} [CommRing S] (s : S) (h : IsUnit (4 * s))
    (ht : Transcendental ℤ s) : Function.Injective (specialize s h) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers denominator) _).mpr
  intro x y
  constructor
  · exact congrArg _
  · simp only [specialize, IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact fun he => congrArg _ (transcendental_iff_injective.mp ht he)

private theorem padicUnit (v : ℤ_[3]) : IsUnit (4 * (4 + 9 * v)) := by
  by_contra hn
  obtain ⟨w, hw⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp hn)
  have h := congrArg (PadicInt.toZMod (p := 3)) hw
  norm_num [map_add, map_mul, map_ofNat] at h
  have h3 : (3 : ZMod 3) = 0 := rfl
  have h9 : (9 : ZMod 3) = 0 := rfl
  simp only [h3, h9, zero_mul, add_zero] at h
  exact (by decide : (4 : ZMod 3) * 4 ≠ 0) h

private abbrev Residue (n : ℕ) := ZMod (3 ^ (n + 1))

private def reduceCoeff (v : ℤ_[3]) (n : ℕ) : CoeffRing →+* Residue n :=
  (PadicInt.toZModPow (n + 1)).comp (specialize _ (padicUnit v))

private def reduceUnit (v : ℤ_[3]) (n : ℕ) := Units.map (reduceCoeff v n).toMonoidHom

private theorem level_alpha (v : ℤ_[3]) (n : ℕ) : ↑(reduceUnit v n alpha) = (4 : Residue n) := by
  simp [reduceUnit, reduceCoeff, spec_alpha, map_ofNat]

private theorem level_delta (v : ℤ_[3]) (n : ℕ) :
    ↑(reduceUnit v n delta) = (4 + 9 * PadicInt.toZModPow (n + 1) v : Residue n) := by
  simp [reduceUnit, reduceCoeff, spec_delta, map_ofNat]

-- At each level 4 and the determinant X = 4 + 9v generate the same subgroup of units.
private theorem level_orders (v : ℤ_[3]) (n : ℕ) :
    orderOf (reduceUnit v n delta) = 3 ^ n ∧ orderOf (reduceUnit v n alpha) = 3 ^ n := by
  simp only [← orderOf_injective _ Units.coeHom_injective, Units.coeHom_apply, level_alpha,
    level_delta]
  constructor
  · let t := PadicInt.toZModPow (n + 1) v
    convert ZMod.orderOf_one_add_mul_prime Nat.prime_three (by decide) (1 + 3 * (t.val : ℤ))
      (by omega) n using 2
    push_cast
    simp [t]
    ring
  · convert ZMod.orderOf_one_add_prime Nat.prime_three (by decide) n using 2
    norm_num

private theorem exponent_exists (v : ℤ_[3]) (n : ℕ) :
    ∃ r : ℤ, reduceUnit v n delta ^ r = reduceUnit v n alpha := by
  let := ZMod.isCyclic_units_of_prime_pow 3 Nat.prime_three (by decide) (n + 1)
  change reduceUnit v n alpha ∈ Subgroup.zpowers (reduceUnit v n delta)
  apply Subgroup.zpowers_le.mp (IsCyclic.subgroup_le_iff_card_dvd.mpr ?_)
  simp only [Nat.card_zpowers, (level_orders v n).1, (level_orders v n).2, dvd_refl]

-- Each finite group must satisfy the whole tail starting at some index.
-- A subdirect product of two members can use the larger of their two indices.
private def eventualLaws (w : ℕ → FreeGroup ℕ) : GroupClass := fun G _ =>
  Finite G ∧ IsPGroup 3 G ∧ ∃ k, ∀ n ≥ k, ∀ f : FreeGroup ℕ →* G, f (w n) = 1

private theorem laws_descend {W : Set (FreeGroup ℕ)} {G H : Type} [Group G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π) (h : SatisfiesLaws W G) : SatisfiesLaws W H := by
  intro w hw f
  let φ := FreeGroup.lift (fun i => (hπ (f (.of i))).choose)
  have he : π.comp φ = f := FreeGroup.ext_hom _ _ fun i => by
    simpa [φ] using (hπ (f (.of i))).choose_spec
  rw [← he, MonoidHom.comp_apply, h w hw φ, map_one]

private theorem eventual_image {w : ℕ → FreeGroup ℕ} {G H : Type} [Group G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π) (h : eventualLaws w G) : eventualLaws w H := by
  obtain ⟨_, hp, k, hk⟩ := h
  refine ⟨Finite.of_surjective π hπ, hp.of_surjective π hπ, k, fun n hn f => ?_⟩
  exact laws_descend (W := {w n}) π hπ (by simpa [SatisfiesLaws] using hk n hn)
    _ (Set.mem_singleton _) f

private theorem eventual_formation (w : ℕ → FreeGroup ℕ) : IsFormation (eventualLaws w) where
  finite _ _ h := h.1
  nonempty := ⟨PUnit, inferInstance, inferInstance, IsPGroup.of_subsingleton _ _, 0,
    fun _ _ _ => Subsingleton.elim ..⟩
  of_mulEquiv _ _ _ _ e := eventual_image e.toMonoidHom e.surjective
  quotient _ _ N _ := eventual_image (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  subdirect G _ _ M N _ _ hM hN := by
    let φ := (QuotientGroup.mk' M).prod (QuotientGroup.mk' N)
    have he : φ.ker = M ⊓ N := by simp [φ, MonoidHom.ker_prod, QuotientGroup.ker_mk']
    apply eventual_image (QuotientGroup.quotientMulEquivOfEq he).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq he).surjective
    let ψ := QuotientGroup.kerLift φ
    obtain ⟨_, hm, k, hk⟩ := hM
    obtain ⟨_, hn, l, hl⟩ := hN
    have hp : IsPGroup 3 ((G ⧸ M) × (G ⧸ N)) := by
      obtain ⟨m, hm⟩ := hm.exists_card_eq
      obtain ⟨n, hn⟩ := hn.exists_card_eq
      exact IsPGroup.of_card (n := m + n) (by rw [Nat.card_prod, hm, hn, pow_add])
    refine ⟨inferInstance, hp.of_injective ψ (QuotientGroup.kerLift_injective _),
      max k l, ?_⟩
    intro i hi f
    apply QuotientGroup.kerLift_injective φ
    rw [map_one]
    exact Prod.ext
      (hk i ((le_max_left ..).trans hi) (((MonoidHom.fst ..).comp ψ).comp f))
      (hl i ((le_max_right ..).trans hi) (((MonoidHom.snd ..).comp ψ).comp f))

private theorem reduce_exponent (v : ℤ_[3]) {m n : ℕ} (hmn : m ≤ n) {r : ℤ}
    (h : reduceUnit v n delta ^ r = reduceUnit v n alpha) :
    reduceUnit v m delta ^ r = reduceUnit v m alpha := by
  let π := ZMod.castHom (pow_dvd_pow 3 (Nat.succ_le_succ hmn)) (Residue m)
  have hπ (u : CoeffRingˣ) : Units.map π.toMonoidHom (reduceUnit v n u) = reduceUnit v m u := by
    apply Units.ext
    exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow (m + 1) (n + 1)
      (Nat.succ_le_succ hmn)) _
  simpa only [map_zpow, hπ] using congrArg (Units.map π.toMonoidHom) h

private theorem separate (v : ℤ_[3]) (hv : Transcendental ℤ (4 + 9 * v)) {x y : CoeffRing}
    (h : ∀ n, reduceCoeff v n x = reduceCoeff v n y) : x = y := by
  apply spec_inj _ (padicUnit v) hv
  apply PadicInt.ext_of_toZModPow.mp
  rintro (_ | n)
  · change (_ : ZMod 1) = _
    exact Subsingleton.elim ..
  · exact h n

-- A word identity that holds at every finite level holds in the generic group:
-- the coefficient map is injective and the reductions separate 3-adic integers.
private theorem eq_one_of_reductions (v : ℤ_[3]) (hv : Transcendental ℤ (4 + 9 * v))
    {g : Triangular alpha beta}
    (h : ∀ n, triMap (reduceCoeff v n) rfl rfl g = 1) : g = 1 := by
  ext1
  · apply Subtype.ext
    apply Prod.ext <;> apply Units.ext <;> apply separate v hv <;> intro n
    · simpa [triMap, tri_one, triangularOne, weight₁, weight₂] using
        congrArg (fun u => (weight₁ u.t : Residue n)) (h n)
    · simpa [triMap, tri_one, triangularOne, weight₁, weight₂] using
        congrArg (fun u => (weight₂ u.t : Residue n)) (h n)
  all_goals apply separate v hv; intro n
  · simpa [triMap, tri_one, triangularOne] using congrArg Triangular.x (h n)
  · simpa [triMap, tri_one, triangularOne] using congrArg Triangular.y (h n)
  · simpa [triMap, tri_one, triangularOne] using congrArg Triangular.z (h n)

private theorem laws_at_one {W : Set (FreeGroup ℕ)} (h : SatisfiesLaws W (Triangular alpha beta)) :
    SatisfiesLaws W (Triangular four four⁻¹) := by
  have hu : IsUnit (4 * (1 : M)) := by rw [mul_one]; exact four.isUnit
  let f := specialize (1 : M) hu
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨z, map_intCast f z⟩
  have ha : Units.map f.toMonoidHom alpha = four := Units.ext (spec_alpha 1 hu)
  have hd : Units.map f.toMonoidHom delta = 1 := Units.ext (spec_delta 1 hu)
  have hb : Units.map f.toMonoidHom beta = four⁻¹ := by rw [beta, _root_.map_div, ha, hd, one_div]
  exact laws_descend _ (triMap_surjective f hs ha hb) h


/--
**Kourovka Problem 11.21 has a negative answer.** There are a prime $p$ and a formation
$\mathfrak F$ all of whose members are $p$-groups such that for every set $W$ of laws, words in the
free group on countably many generators, some finite $p$-group lies in $\mathfrak F$ and fails a
law in $W$, or satisfies every law in $W$ and does not lie in $\mathfrak F$. Thus $\mathfrak F$ is
not of the form $\mathfrak N_p \cap \mathfrak M$ for any variety $\mathfrak M$, where
$\mathfrak N_p$ is the formation of all finite $p$-groups.

The Kourovka Archive answers 11.21 "No, it is not true" (A. N. Krasil'nikov): formations of finite
$p$-groups correspond bijectively to varieties of pro-$p$ groups, there are continuously many
varieties of nilpotent pro-$p$ groups of class at most $6$ (Zubkov), hence continuously many
formations of finite $p$-groups of class at most $6$, while such a formation of the form
$\mathfrak N_p \cap \mathfrak M$ equals $\mathfrak N_p \cap (\mathfrak M \cap \mathfrak N_6)$, where
$\mathfrak N_6$ is the variety of nilpotent groups of class at most $6$, and there are only
countably many varieties of nilpotent groups of class at most $6$ (all finitely based).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 11.21 (A. F. Vasil'yev); resolution: A. N. Krasil'nikov, letter of 17 July
1998, using A. N. Zubkov, Siberian Math. J. 29, no. 3 (1988), 491-494, Kourovka Archive, Problem
11.21: "No, it is not true"; formations of finite `p`-groups correspond to varieties of pro-`p`
groups, there are continuously many varieties of nilpotent pro-`p` groups of class at most 6
(Zubkov) but only countably many varieties of nilpotent groups of class at most 6,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem subformationOfPGroupsIsVarietal_refuted : ¬ subformationOfPGroupsIsVarietal := by
  intro hall
  obtain ⟨v, hv⟩ := coefficient_choice
  choose r hr using exponent_exists v
  let w := fun n => testWord (r n)
  obtain ⟨W, hW⟩ := hall 3 Nat.prime_three (eventualLaws w) (eventual_formation w)
    (fun _ _ h => h.2.1)
  -- Each finite reduction satisfies every test word from its own level onward.
  have hlevels (n : ℕ) :
      SatisfiesLaws W (Triangular (reduceUnit v n alpha) (reduceUnit v n beta)) := by
    obtain ⟨hd, ha⟩ := level_orders v n
    have hpow {u : (Residue n)ˣ} (h : orderOf u = 3 ^ n) : u ^ 3 ^ n = 1 := h ▸ pow_orderOf_eq_one u
    have hp := triPGroup (hpow ha) (b := reduceUnit v n beta) (by
      simp [beta, div_pow, hpow hd, hpow ha])
    apply (hW _ hp).mp
    refine ⟨inferInstance, hp, n, fun m hm => testWord_eq_one _ ?_⟩
    simpa [beta] using reduce_exponent v hm (hr m)
  -- Ordinary laws pass through the generic group to the specialization X = 1.
  have hgeneric : SatisfiesLaws W (Triangular alpha beta) := by
    intro s hs f
    apply eq_one_of_reductions v hv
    exact fun n => hlevels n s hs ((triMap (reduceCoeff v n) rfl rfl).comp f)
  have hfour : four ^ (3 ^ 4) = 1 := by decide
  have ht := (hW _ (triPGroup hfour (by rw [inv_pow, hfour, inv_one]))).mpr (laws_at_one hgeneric)
  obtain ⟨k, hk⟩ := ht.2.2
  obtain ⟨f, hf⟩ := specialization_fails (r k)
  exact hf (hk k le_rfl f)

end

end MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted
