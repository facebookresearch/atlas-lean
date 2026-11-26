/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Refutation of Kourovka Problem 12.26

The affine group of the plane over `ZMod 3` has a `2`-block of defect zero, while every element in
its largest normal subgroup of odd order has even centralizer order.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/DefectZeroBlockCentralizerKourovka12Problem26Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.26 (Shi
Shengming; Jiping Zhang). UnsolvedMath record UM-00700845 (`KOU-12.26`), dataset ulamai/UnsolvedMath
v1.8.0.

A `p`-block of defect zero is encoded by its unique irreducible complex character `χ`, which is
characterized by `|G|ₚ ∣ χ(1)` (Brauer): `G` has one exactly when some irreducible complex
representation has degree divisible by `p^{vₚ(|G|)}`. `O_{p'}(G)` is the largest normal subgroup of
order prime to `p`, so `x ∈ O_{p'}(G)` is stated as `x ∈ N` for some normal subgroup `N` of order
prime to `p`. `p`-soluble means a subnormal series whose factors are `p`-groups or have order prime
to `p`.
-/

namespace MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26Wanted

@[expose] public section

/-- **$p$-soluble groups.** Let $p$ be a natural number. A group $G$ is $p$-soluble when it has a
subnormal series $1 = H_0 \le H_1 \le \dots \le H_n = G$, each $H_i$ normal in $H_{i+1}$, whose
factors $H_{i+1}/H_i$ are $p$-groups or have order prime to $p$. Here an infinite factor is taken
to have order $0$. -/
def IsPSoluble (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsPGroup p (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ∨
          (Nat.card (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))).Coprime p

/-- **Groups with a $p$-block of defect zero.** Let $p$ be a natural number. A group $G$ has a
$p$-block of defect zero when some irreducible finite-dimensional complex representation of $G$ has
degree divisible by $p^{v_p(|G|)}$, where $v_p(|G|)$ is the exponent of $p$ in the prime
factorization of the order $|G|$ of $G$ (this exponent is $0$ when $p$ is not prime or $G$ is
infinite). For a prime $p$ and a finite group $G$, the number $p^{v_p(|G|)}$ is $|G|_p$, the largest
power of $p$ dividing $|G|$.

By Brauer's theory the $p$-blocks of defect zero are exactly the singletons $\{\chi\}$ with $\chi$
irreducible and $|G|_p \mid \chi(1)$. -/
def HasDefectZeroBlock (p : ℕ) (G : Type) [Group G] : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧
      p ^ (Nat.card G).factorization p ∣ Module.finrank ℂ V

/-- **Kourovka Problem 12.26.** This is the proposition (Shi Shengming) that for every prime $p$ and
every finite $p$-soluble group $G$, the group $G$ has a $p$-block of defect zero if and only if some
normal subgroup $N$ of $G$ of order prime to $p$ contains an element $x$ whose centralizer $C_G(x)$
in $G$ has order prime to $p$.

Equivalently, some $x \in O_{p'}(G)$ has a centralizer of order prime to $p$, since $O_{p'}(G)$ is
the largest normal subgroup of $G$ of order prime to $p$. -/
def defectZeroBlockIffPRegularCentralizer : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPSoluble p G →
    (HasDefectZeroBlock p G ↔
      ∃ N : Subgroup G, N.Normal ∧ (Nat.card N).Coprime p ∧
        ∃ x ∈ N, (Nat.card (Subgroup.centralizer {x})).Coprime p)

end

open Matrix

private abbrev F := ZMod 3
private abbrev Vec := Fin 2 → F
private abbrev Mat := Matrix (Fin 2) (Fin 2) F
private abbrev H := GL (Fin 2) F

private lemma square_eq_one_of_ne_zero : ∀ a : F, a ≠ 0 → a * a = 1 := by decide

-- Over `ZMod 3`, the inverse of a nonzero determinant is the determinant itself.
-- The explicit adjugate keeps the finite checks in kernel computation.
private def matrixUnit (A : Mat) (hA : A.det ≠ 0) : H where
  val := A
  inv := A.det • !![A 1 1, -A 0 1; -A 1 0, A 0 0]
  val_inv := by
    rw [← Matrix.adjugate_fin_two, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul,
      square_eq_one_of_ne_zero _ hA, one_smul]
  inv_val := by
    rw [← Matrix.adjugate_fin_two, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
      square_eq_one_of_ne_zero _ hA, one_smul]

private def matrixUnits : {A : Mat // A.det ≠ 0} ≃ H where
  toFun A := matrixUnit A.1 A.2
  invFun a := ⟨a.val, a.det_ne_zero⟩
  left_inv _ := rfl
  right_inv _ := Units.ext rfl

local instance fintypeLinear : Fintype H := Fintype.ofEquiv _ matrixUnits

private lemma card_H : Fintype.card H = 48 := by decide

private def translationAction : H →* MulAut (Multiplicative Vec) where
  toFun a := (Matrix.GeneralLinearGroup.toLin a).toLinearEquiv.toAddEquiv.toMultiplicative
  map_one' := by ext; simp
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    change (a.val * b.val) *ᵥ x.toAdd = a.val *ᵥ (b.val *ᵥ x.toAdd)
    rw [Matrix.mulVec_mulVec]

private abbrev G := Multiplicative Vec ⋊[translationAction] H

private def groupEquiv : G ≃ Vec × H where
  toFun g := (g.left.toAdd, g.right)
  invFun g := ⟨Multiplicative.ofAdd g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

local instance fintypeAffine : Fintype G := Fintype.ofEquiv _ groupEquiv.symm

private lemma card_G : Nat.card G = 432 := by
  rw [Nat.card_congr groupEquiv, Nat.card_eq_fintype_card]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  decide

private lemma row_ne_zero (a : H) : a.val 0 ≠ 0 := by
  intro h
  have hd := a.det_ne_zero
  rw [Matrix.det_fin_two, show a.val 0 0 = 0 from congrFun h 0,
    show a.val 0 1 = 0 from congrFun h 1] at hd
  simp at hd

-- A coset of the lower unitriangular subgroup is specified by the first row
-- and determinant of its matrix representative.
private abbrev Index := {v : Vec // v ≠ 0} × Fˣ

local instance decidableEqIndex : DecidableEq Index := by unfold Index; infer_instance

private def index (a : H) : Index := (⟨a.val 0, row_ne_zero a⟩, a.det)

private def sectionMatrix (i : Index) : Mat :=
  !![i.1.val 0, i.1.val 1;
    if i.1.val 0 = 0 then -(i.2 : F) * i.1.val 1 else 0,
    if i.1.val 0 = 0 then 0 else (i.2 : F) * i.1.val 0]

private lemma sectionMatrix_det (i : Index) : (sectionMatrix i).det = i.2 := by
  have h := i.1.property
  rw [Matrix.det_fin_two]
  change i.1.val 0 * (if i.1.val 0 = 0 then 0 else (i.2 : F) * i.1.val 0) -
    i.1.val 1 * (if i.1.val 0 = 0 then -(i.2 : F) * i.1.val 1 else 0) = i.2
  split_ifs with hzero
  · have hother : i.1.val 1 ≠ 0 := by
      intro h1
      apply h
      funext j
      fin_cases j <;> assumption
    simp only [hzero, zero_mul, zero_sub]
    rw [show -(i.1.val 1 * (-(i.2 : F) * i.1.val 1)) =
      (i.2 : F) * (i.1.val 1 * i.1.val 1) by ring,
      square_eq_one_of_ne_zero _ hother, mul_one]
  · rw [mul_zero, sub_zero, show i.1.val 0 * ((i.2 : F) * i.1.val 0) =
      (i.2 : F) * (i.1.val 0 * i.1.val 0) by ring,
      square_eq_one_of_ne_zero _ hzero, mul_one]

private def sectionGL (i : Index) : H :=
  matrixUnit (sectionMatrix i) (sectionMatrix_det i ▸ i.2.ne_zero)

private lemma index_sectionGL (i : Index) : index (sectionGL i) = i := by
  apply Prod.ext
  · apply Subtype.ext
    funext j
    fin_cases j <;> rfl
  · apply Units.ext
    exact sectionMatrix_det i

private def step (i : Index) (a : H) : Index := index (sectionGL i * a)

private lemma step_one (i : Index) : step i 1 = i := by
  simp [step, index_sectionGL]

private lemma index_mul_congr {a b : H} (h : index a = index b) (c : H) :
    index (a * c) = index (b * c) := by
  apply Prod.ext
  · apply Subtype.ext
    have hr : a.val 0 = b.val 0 := congrArg (fun i : Index => i.1.val) h
    change a.val 0 ᵥ* c.val = b.val 0 ᵥ* c.val
    rw [hr]
  · change (a * c).det = (b * c).det
    rw [map_mul, map_mul, show a.det = b.det from congrArg Prod.snd h]

private lemma step_mul (i : Index) (a b : H) : step (step i a) b = step i (a * b) := by
  change index (sectionGL (step i a) * b) = index (sectionGL i * (a * b))
  rw [← mul_assoc]
  exact index_mul_congr (index_sectionGL (step i a)) b

private lemma step_transitive (i j : Index) : ∃ a : H, step i a = j :=
  ⟨(sectionGL i)⁻¹ * sectionGL j, by simp [step, index_sectionGL]⟩

-- For representatives `sᵢ`, decompose `sᵢ g` as a translation and an element of the
-- lower unitriangular subgroup, followed by `sⱼ` for the new coordinate `j`.
private def linearPart (g : G) (i : Index) : H :=
  sectionGL i * g.right * (sectionGL (step i g.right))⁻¹

private lemma linearPart_index (g : G) (i : Index) : index (linearPart g i) = index 1 := by
  unfold linearPart
  simpa using index_mul_congr (index_sectionGL (step i g.right)).symm
    (sectionGL (step i g.right))⁻¹

private def translationPart (g : G) (i : Index) : Vec := (sectionGL i).val *ᵥ g.left.toAdd

-- The first translation coordinate and the lower-left matrix entry give an additive
-- character of the stabilizer. Their sum is the exponent for induction.
private def phase (g : G) (i : Index) : F := translationPart g i 0 + (linearPart g i).val 1 0

private lemma phase_one (i : Index) : phase 1 i = 0 := by
  simp [phase, translationPart, linearPart, step_one]

private lemma phase_mul (g h : G) (i : Index) :
    phase (g * h) i = phase g i + phase h (step i g.right) := by
  have hl (a : G) (j : Index) : (linearPart a j).val 0 = (1 : Mat) 0 :=
    congrArg (fun i : Index => i.1.val) (linearPart_index a j)
  have hdet (a : G) (j : Index) : (linearPart a j).val.det = 1 :=
    congrArg (fun i : Index => (i.2 : F)) (linearPart_index a j)
  have h00 (a : G) (j : Index) : (linearPart a j).val 0 0 = 1 := by
    rw [hl]; simp
  have h01 (a : G) (j : Index) : (linearPart a j).val 0 1 = 0 := by
    rw [hl]; simp
  have h11 (a : G) (j : Index) : (linearPart a j).val 1 1 = 1 := by
    simpa [Matrix.det_fin_two, h00, h01] using hdet a j
  have hlin : linearPart (g * h) i = linearPart g i * linearPart h (step i g.right) := by
    simp [linearPart, ← step_mul, mul_assoc]
  have htrans : translationPart (g * h) i =
      translationPart g i + (linearPart g i).val *ᵥ translationPart h (step i g.right) := by
    change (sectionGL i).val *ᵥ (g.left.toAdd + g.right.val *ᵥ h.left.toAdd) = _
    simp [translationPart, Matrix.mulVec_add, Matrix.mulVec_mulVec, linearPart, mul_assoc]
  simp only [phase, hlin, htrans, Pi.add_apply, Units.val_mul]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h01, h11]
  ring

private lemma card_Index : Fintype.card Index = 16 := by decide

private def inLinear (a : H) : G := SemidirectProduct.inr a
private def inTranslation (v : Vec) : G := SemidirectProduct.inl (Multiplicative.ofAdd v)

private def basisVec (j : Fin 2) : Vec := fun k => if k = j then 1 else 0

private lemma phase_inTranslation (v : Vec) (i : Index) :
    phase (inTranslation v) i = (i.1.val ⬝ᵥ v) := by
  have hr : (sectionGL i).val 0 = i.1.val :=
    congrArg (fun i : Index => i.1.val) (index_sectionGL i)
  simp [phase, inTranslation, translationPart, linearPart, step_one, Matrix.mulVec, hr]

private def shear : H := matrixUnit !![1, 0; 1, 1] (by decide)

private def conjugateShear (i : Index) : H := (sectionGL i)⁻¹ * shear * sectionGL i

private lemma shear_fixes (i : Index) : step i (conjugateShear i) = i := by
  have h : index shear = index 1 := by decide
  unfold step conjugateShear
  rw [← mul_assoc (sectionGL i) ((sectionGL i)⁻¹ * shear) (sectionGL i), mul_inv_cancel_left,
    index_mul_congr h, one_mul, index_sectionGL]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The decision procedure compares pairs of oriented rows.
private lemma shear_distinguishes : ∀ i j : Index, i.1 = j.1 → i ≠ j →
    step j (conjugateShear i) = j ∧
      phase (inLinear (conjugateShear i)) i ≠ phase (inLinear (conjugateShear i)) j := by
  decide

private lemma phase_separates {i j : Index} (h : i ≠ j) :
    ∃ g : G, step i g.right = i ∧ step j g.right = j ∧ phase g i ≠ phase g j := by
  by_cases hr : i.1 = j.1
  · obtain ⟨hj, hp⟩ := shear_distinguishes i j hr h
    exact ⟨inLinear (conjugateShear i), shear_fixes i, hj, hp⟩
  · have hv : i.1.val ≠ j.1.val := fun h => hr (Subtype.ext h)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    refine ⟨inTranslation (basisVec k), step_one i, step_one j, ?_⟩
    rw [phase_inTranslation, phase_inTranslation]
    fin_cases k <;> simpa [basisVec, dotProduct, Fin.sum_univ_two] using hk

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The decision procedure searches the linear group for each translation vector.
private lemma reflection_exists : ∀ v : Vec, ∃ a : H, a ≠ 1 ∧ a * a = 1 ∧ a.val *ᵥ v = v := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The decision procedure searches the linear group for suitable conjugates.
private lemma third_power_obstruction : ∀ a : H, a ^ 3 = 1 → a ≠ 1 →
    ∃ b : H, (a * (b * a * b⁻¹)) ^ 3 ≠ 1 := by
  decide

-- The quaternion subgroup of `SL₂(3)` consists of the two scalar matrices and the
-- determinant-one matrices of trace zero. Its closure and normality are finite checks.
private def quaternionMem (a : H) : Bool :=
  decide (a.det = 1 ∧ (a.val.trace = 0 ∨ a = 1 ∨ a = -1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The decision procedure checks products in the linear group.
private lemma quaternion_mul : ∀ a b : H, quaternionMem a → quaternionMem b →
    quaternionMem (a * b) := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The decision procedure checks the inverses of quaternion subgroup elements.
private lemma quaternion_inv : ∀ a : H, quaternionMem a → quaternionMem a⁻¹ := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The decision procedure checks conjugation by every element of the linear group.
private lemma quaternion_conj : ∀ a b : H, quaternionMem a → quaternionMem (b * a * b⁻¹) := by
  decide

private def quaternion : Subgroup H where
  carrier := {a | quaternionMem a}
  one_mem' := by decide
  mul_mem' {a b} := quaternion_mul a b
  inv_mem' {a} := quaternion_inv a

private instance quaternionNormal : quaternion.Normal := ⟨fun a ha b => quaternion_conj a b ha⟩

private lemma card_quaternion : Nat.card quaternion = 8 := by
  let : Fintype quaternion := Fintype.subtype (Finset.univ.filter (fun a => quaternionMem a)) (by
    intro a
    simp [quaternion])
  rw [Nat.card_eq_fintype_card]
  decide

private lemma card_detKer : Nat.card ((Matrix.GeneralLinearGroup.det : H →* Fˣ).ker) = 24 := by
  let : Fintype ((Matrix.GeneralLinearGroup.det : H →* Fˣ).ker) :=
    Fintype.subtype (Finset.univ.filter
      (fun a => (Matrix.GeneralLinearGroup.det (R := F) (n := Fin 2)) a = 1)) (by simp)
  rw [Nat.card_eq_fintype_card]
  decide

private noncomputable def cubeRoot : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / (3 : ℕ))

private lemma cubeRoot_primitive : IsPrimitiveRoot cubeRoot 3 :=
  Complex.isPrimitiveRoot_exp 3 (by decide)

private noncomputable def phaseChar : AddChar F ℂ :=
  AddChar.zmodChar 3 cubeRoot_primitive.pow_eq_one

private lemma phaseChar_injective : Function.Injective phaseChar := by
  intro x y h
  rw [phaseChar, AddChar.zmodChar_apply, AddChar.zmodChar_apply] at h
  exact ZMod.val_injective _ (cubeRoot_primitive.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)

private abbrev RepSpace := Index → ℂ

private noncomputable def affineRep : Representation ℂ G RepSpace where
  toFun g :=
    { toFun := fun w i => phaseChar (phase g i) * w (step i g.right)
      map_add' := by intros; funext i; exact mul_add _ _ _
      map_smul' := by intros; funext i; simp [mul_left_comm] }
  map_one' := by ext w i; simp [phase_one, step_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    funext i
    change phaseChar (phase (g * h) i) * w (step i (g.right * h.right)) =
      phaseChar (phase g i) * (phaseChar (phase h (step i g.right)) *
        w (step (step i g.right) h.right))
    rw [phase_mul, AddChar.map_add_eq_mul, step_mul, mul_assoc]

private lemma affineRep_apply (g : G) (w : RepSpace) (i : Index) :
    affineRep g w i = phaseChar (phase g i) * w (step i g.right) := rfl

private def coordinate (i : Index) : RepSpace := Pi.single i 1

private lemma step_injective (a : H) : Function.Injective (fun i => step i a) := by
  intro i j h
  simpa only [step_mul, mul_inv_cancel, step_one] using congrArg (fun k => step k a⁻¹) h

private lemma affineRep_coordinate {g : G} {i j : Index} (h : step i g.right = j) :
    affineRep g (coordinate j) = phaseChar (phase g i) • coordinate i := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [coordinate, affineRep_apply, h]
  · have hk' : step k g.right ≠ j := fun h' => hk (step_injective g.right (h'.trans h.symm))
    simp [coordinate, affineRep_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk']

private lemma affineRep_intertwiner_diagonal
    (f : Representation.IntertwiningMap affineRep affineRep) {i j : Index} (h : i ≠ j) :
    f (coordinate j) i = 0 := by
  obtain ⟨g, hi, hj, hp⟩ := phase_separates h
  have hc := congrFun (Representation.IntertwiningMap.isIntertwining _ _ f g (coordinate j)) i
  rw [affineRep_coordinate hj, map_smul, Pi.smul_apply, smul_eq_mul, affineRep_apply, hi] at hc
  apply (mul_eq_zero.mp (show (phaseChar (phase g j) - phaseChar (phase g i)) *
      f (coordinate j) i = 0 by rw [sub_mul, hc, sub_self])).resolve_left
  exact sub_ne_zero.mpr (fun he => hp (phaseChar_injective he.symm))

private lemma affineRep_intertwiner_scalar
    (f : Representation.IntertwiningMap affineRep affineRep) :
    ∃ c : ℂ, ∀ w : RepSpace, f w = c • w := by
  let i₀ : Index := index 1
  refine ⟨f (coordinate i₀) i₀, ?_⟩
  have hdiag (i : Index) : f (coordinate i) i = f (coordinate i₀) i₀ := by
    obtain ⟨a, ha⟩ := step_transitive i i₀
    let g := inLinear a
    have hstep : step i g.right = i₀ := ha
    have hc := congrFun (Representation.IntertwiningMap.isIntertwining _ _ f g (coordinate i₀)) i
    rw [affineRep_coordinate hstep, map_smul, Pi.smul_apply, smul_eq_mul, affineRep_apply,
      hstep] at hc
    exact mul_left_cancel₀ (phaseChar.val_isUnit (phase g i)).ne_zero hc
  have hcoord (i : Index) : f (coordinate i) = f (coordinate i₀) i₀ • coordinate i := by
    funext j
    by_cases hij : j = i
    · subst j
      simpa [coordinate] using hdiag i
    · rw [affineRep_intertwiner_diagonal f hij]
      simp [coordinate, Pi.single_eq_of_ne hij]
  intro w
  have hw : (∑ i : Index, w i • coordinate i) = w := by
    funext j
    simp [coordinate, Finset.sum_apply, Pi.single_apply]
  rw [← hw, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hcoord, smul_comm]

open scoped MonoidAlgebra in
private lemma affineRep_irreducible : affineRep.IsIrreducible := by
  have : Nonempty Index := ⟨index 1⟩
  have : Nontrivial affineRep.asModule := inferInstanceAs (Nontrivial RepSpace)
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_pos (α := G)).ne'⟩
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  -- By Maschke, each submodule has an equivariant projection. Scalar projections
  -- with nonzero image are the identity.
  apply IsSimpleOrder.of_forall_eq_top
  intro P hP
  obtain ⟨r, hr⟩ := MonoidAlgebra.exists_leftInverse_of_injective (k := ℂ) (G := G)
    (V := P) (W := affineRep.asModule) P.subtype P.ker_subtype
  let t := (Representation.IntertwiningMap.equivLinearMapAsModule affineRep affineRep).symm
    (P.subtype.comp r)
  have ht (w : RepSpace) : t w = (P.subtype.comp r) (show affineRep.asModule from w) := rfl
  obtain ⟨c, hc⟩ := affineRep_intertwiner_scalar t
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff P).mp hP
  have hrv := DFunLike.congr_fun hr (⟨v, hv⟩ : P)
  have hc1 : c = 1 := by
    have hcv : c • (show RepSpace from v) = v := by
      rw [← hc, ht]
      exact congrArg P.subtype hrv
    exact smul_left_injective ℂ (show (v : RepSpace) ≠ 0 from hv0)
      (hcv.trans (one_smul ℂ _).symm)
  apply top_unique
  intro w _
  have hw := hc (show RepSpace from w)
  rw [ht, hc1, one_smul] at hw
  exact hw ▸ (r w).property

private def projection : G →* H := SemidirectProduct.rightHom

private abbrev detKer : Subgroup H := (Matrix.GeneralLinearGroup.det : H →* Fˣ).ker

private lemma card_comap_projection (K : Subgroup H) :
    Nat.card (K.comap projection) = 9 * Nat.card K := by
  let e : K.comap projection ≃ Vec × K :=
    { toFun := fun g => (g.val.left.toAdd, ⟨g.val.right, g.property⟩)
      invFun := fun v => ⟨⟨Multiplicative.ofAdd v.1, v.2.val⟩, v.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  rfl

private lemma quotient_card {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (B ⧸ A.subgroupOf B) = Nat.card B / Nat.card A := by
  rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

-- Pull back the chain `1 ≤ Q₈ ≤ SL₂(3) ≤ GL₂(3)` along the projection to `GL₂(3)`.
private lemma pSoluble_witness : IsPSoluble 2 G := by
  let T : Subgroup G := (⊥ : Subgroup H).comap projection
  let Q : Subgroup G := quaternion.comap projection
  let S : Subgroup G := detKer.comap projection
  have hTQ : T ≤ Q := Subgroup.comap_mono bot_le
  have hQS : Q ≤ S := Subgroup.comap_mono (fun a ha => by
    change a.det = 1
    have hm : quaternionMem a = true := ha
    simp only [quaternionMem, decide_eq_true_eq] at hm
    exact hm.1)
  have hT : Nat.card T = 9 := by
    rw [card_comap_projection, Subgroup.card_bot, mul_one]
  have hQ : Nat.card Q = 72 := by rw [card_comap_projection, card_quaternion]
  have hS : Nat.card S = 216 := by rw [card_comap_projection, card_detKer]
  have hTop : Nat.card (⊤ : Subgroup G) = 432 := by rw [Subgroup.card_top, card_G]
  have stepCoprime {A B : Subgroup G} [A.Normal] (h : A ≤ B)
      (hc : (Nat.card B / Nat.card A).Coprime 2) :
      A ≤ B ∧ ∃ _ : (A.subgroupOf B).Normal,
        IsPGroup 2 (B ⧸ A.subgroupOf B) ∨ (Nat.card (B ⧸ A.subgroupOf B)).Coprime 2 :=
    ⟨h, inferInstance, Or.inr ((quotient_card h).symm ▸ hc)⟩
  have stepPower {A B : Subgroup G} [A.Normal] (h : A ≤ B) {n : ℕ}
      (hc : Nat.card B / Nat.card A = 2 ^ n) :
      A ≤ B ∧ ∃ _ : (A.subgroupOf B).Normal,
        IsPGroup 2 (B ⧸ A.subgroupOf B) ∨ (Nat.card (B ⧸ A.subgroupOf B)).Coprime 2 :=
    ⟨h, inferInstance, Or.inl (IsPGroup.of_card ((quotient_card h).trans hc))⟩
  refine ⟨4, ![⊥, T, Q, S, ⊤], rfl, rfl, fun i => ?_⟩
  fin_cases i
  · exact stepCoprime (A := ⊥) (B := T) bot_le (by rw [hT, Subgroup.card_bot]; decide)
  · exact stepPower (A := T) (B := Q) hTQ (n := 3) (by rw [hQ, hT]; decide)
  · exact stepCoprime (A := Q) (B := S) hQS (by rw [hS, hQ]; decide)
  · exact stepPower (A := S) (B := ⊤) le_top (n := 1) (by rw [hTop, hS]; decide)

private lemma right_pow_three {N : Subgroup G} (hN : (Nat.card N).Coprime 2)
    {x : G} (hx : x ∈ N) : x.right ^ 3 = 1 := by
  have hd : orderOf x.right ∣ Nat.card N :=
    (orderOf_map_dvd projection x).trans (N.orderOf_dvd_natCard hx)
  have h48 : orderOf x.right ∣ 2 ^ 4 * 3 := by
    rw [show 2 ^ 4 * 3 = (48 : ℕ) by decide]
    simpa only [Nat.card_eq_fintype_card, card_H] using orderOf_dvd_natCard x.right
  exact orderOf_dvd_iff_pow_eq_one.mp
    (((hN.of_dvd_left hd).pow_right 4).dvd_of_dvd_mul_left h48)

-- Normality makes the product of a nonidentity image and any conjugate another image.
-- The finite obstruction above forces one such product to have order not dividing three.
private lemma odd_normal_right_eq_one {N : Subgroup G} (hNormal : N.Normal)
    (hOdd : (Nat.card N).Coprime 2) {x : G} (hx : x ∈ N) : x.right = 1 := by
  by_contra hne
  obtain ⟨a, ha⟩ := third_power_obstruction x.right (right_pow_three hOdd hx) hne
  have hmem : x * (inLinear a * x * (inLinear a)⁻¹) ∈ N :=
    N.mul_mem hx (hNormal.conj_mem x hx (inLinear a))
  have hp := right_pow_three (x := x * (inLinear a * x * (inLinear a)⁻¹)) hOdd hmem
  exact ha hp

private lemma even_centralizer_of_right_eq_one (x : G) (hx : x.right = 1) :
    2 ∣ Nat.card (Subgroup.centralizer {x}) := by
  obtain ⟨a, ha, ha2, hfix⟩ := reflection_exists x.left.toAdd
  have hcommute : inLinear a ∈ Subgroup.centralizer {x} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change inLinear a * x = x * inLinear a
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (0 + a.val *ᵥ x.left.toAdd) =
        x.left * translationAction x.right 1
      simp [hfix]
    · change a * x.right = x.right * a
      simp [hx]
  let y : Subgroup.centralizer {x} := ⟨inLinear a, hcommute⟩
  have hy₂ : y ^ 2 = 1 := by
    apply Subtype.ext
    change (SemidirectProduct.inr a : G) ^ 2 = 1
    rw [← map_pow, pow_two, ha2, map_one]
  have hy₁ : y ≠ 1 := fun h => ha (congrArg (fun y : Subgroup.centralizer {x} => y.val.right) h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa only [orderOf_eq_prime hy₂ hy₁] using orderOf_dvd_natCard y

private lemma counterexample_block : HasDefectZeroBlock 2 G := by
  refine ⟨RepSpace, inferInstance, inferInstance, inferInstance,
    affineRep, affineRep_irreducible, ?_⟩
  rw [card_G, Module.finrank_fintype_fun_eq_card, card_Index]
  have h : (432 : ℕ).factorization 2 = 4 := by
    apply le_antisymm
    · by_contra! h
      have hd := (Nat.prime_two.pow_dvd_iff_le_factorization (n := 432) (by decide)).mpr
        (show 5 ≤ (432 : ℕ).factorization 2 by omega)
      exact (by decide : ¬2 ^ 5 ∣ 432) hd
    · exact (Nat.prime_two.pow_dvd_iff_le_factorization (n := 432) (by decide)).mp (by decide)
  rw [h]
  decide

private lemma counterexample_no_odd_centralizer (N : Subgroup G) (hN : N.Normal)
    (hOdd : (Nat.card N).Coprime 2) (x : G) (hx : x ∈ N) :
    ¬(Nat.card (Subgroup.centralizer {x})).Coprime 2 := by
  have hd := even_centralizer_of_right_eq_one x (odd_normal_right_eq_one hN hOdd hx)
  exact fun hc => (by decide : ¬Nat.Coprime 2 2) (hc.of_dvd_left hd)

/--
**Refutation of Kourovka Problem 12.26.** The proposition of Kourovka Problem 12.26 is false:
it is not the case that for every prime $p$ and every finite $p$-soluble group $G$, the group $G$
has a $p$-block of defect zero if and only if some normal subgroup $N$ of $G$ of order prime to $p$
contains an element $x$ whose centralizer $C_G(x)$ in $G$ has order prime to $p$.

V. I. Zenkov's counterexample: the group $G = 3^2.\mathrm{GL}_2(3)$ of order $432$ is soluble and
has a $2$-block of defect zero (an irreducible character of degree $16$), but the centralizer of
every element of $O_{2'}(G) = 3^2$, the largest normal subgroup of $G$ of odd order, has even order.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.26 (Shi Shengming; Jiping Zhang);
resolution: V. I. Zenkov, Trudy Inst. Mat. i Mekh. UrO RAN 3 (1995), 36-40 (Russian), Kourovka
Archive, Problem 12.26: No; G = 3^2.GL_2(3), p = 2.
-/
public theorem defectZeroBlockIffPRegularCentralizer_refuted :
    ¬ defectZeroBlockIffPRegularCentralizer
 := by
  intro h
  obtain ⟨N, hN, hOdd, x, hx, hc⟩ :=
    (h 2 Nat.prime_two G pSoluble_witness).mp counterexample_block
  exact counterexample_no_odd_centralizer N hN hOdd x hx hc

end MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26Wanted
