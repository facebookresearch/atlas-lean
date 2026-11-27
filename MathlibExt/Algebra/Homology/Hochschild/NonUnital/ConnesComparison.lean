/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic

import Mathlib.Tactic.Abel

/-!
# Rational comparison of the cyclic total and the Connes quotient

Let k be a commutative ring and A a nonunital k-algebra with k-bilinear
multiplication. At vertical degree q, put
t_q(a₀ ⊗ ⋯ ⊗ a_q) = (−1)^q a_q ⊗ a₀ ⊗ ⋯ ⊗ a_(q−1),
N_q = ∑_(i=0)^q t_q^i and W_q = ∑_(i=0)^q i t_q^i.
The horizontal cyclic row has differential 1−t_q into an even position
and N_q into an odd position. It augments to the Connes quotient
Cλ_q(A) = coker(1−t_q) in position zero.

If q+1 is invertible in k and a = (q+1)⁻¹, the row homotopy component
at position p is −a W_q for even p and a id for odd p. Together with
the quotient section represented by a N_q, these maps make the row
augmentation a homotopy equivalence, hence a quasi-isomorphism.

The row augmentations assemble into a bicomplex map. After transposing
and totalizing with the sign (−1)^(pq), its total augmentation is the
cyclic-to-Connes chain map: project the column p = 0 and annihilate
all p > 0 columns. If k is a ℚ-algebra, every q+1 is invertible, so
this chain map induces HC_n(A) ≅ H_n(Cλ(A)) for every n ≥ 0.
Both directions are natural for nonunital algebra maps in the common
module category ModuleCat^max(u,v)(k).

Reference: Loday, *Cyclic Homology*, Theorem 2.1.5 and
equations 2.1.5.1–2.1.5.2.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace ModuleCat.Algebra.Hochschild.NonUnital

universe u v w

private lemma weightedPowerSum_comm {E : Type*} [Ring E] (T : E) (q : ℕ) :
    T * (∑ i ∈ Finset.range (q + 1), i • T ^ i) =
      (∑ i ∈ Finset.range (q + 1), i • T ^ i) * T := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    T * (i • T ^ i) = i • (T * T ^ i) := mul_smul_comm i T (T ^ i)
    _ = i • (T ^ i * T) := congrArg (fun x : E => i • x)
      ((pow_succ' T i).symm.trans (pow_succ T i))
    _ = (i • T ^ i) * T := (smul_mul_assoc i (T ^ i) T).symm

private lemma weightedPowerSum_right {E : Type*} [Ring E] (T : E) (q : ℕ) :
    (∑ i ∈ Finset.range (q + 1), i • T ^ i) * (1 - T) =
      (∑ i ∈ Finset.range (q + 1), T ^ i) - 1 - q • T ^ (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hW : (∑ i ∈ Finset.range ((q + 1) + 1), i • T ^ i) =
          (∑ i ∈ Finset.range (q + 1), i • T ^ i) + (q + 1) • T ^ (q + 1) :=
        Finset.sum_range_succ _ (q + 1)
      have hN : (∑ i ∈ Finset.range ((q + 1) + 1), T ^ i) =
          (∑ i ∈ Finset.range (q + 1), T ^ i) + T ^ (q + 1) :=
        Finset.sum_range_succ _ (q + 1)
      have hp : T ^ (q + 1) * T = T ^ ((q + 1) + 1) :=
        (pow_succ T (q + 1)).symm
      rw [hW, add_mul, ih, hN, smul_mul_assoc, mul_sub, mul_one, hp, nsmul_sub]
      simp only [add_nsmul, one_nsmul]
      abel

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]

/-- Let k be a commutative ring, A a nonunital ring equipped
with a k-module structure, q ≥ 0, and assume q+1 is invertible in k.
With t_q the signed cyclic operator on A ⊗[k] A^⊗q and
W_q = ∑_(i=0)^q i t_q^i, the row homotopy operator in position p is
−(q+1)⁻¹ W_q when p is even and (q+1)⁻¹ id when p is odd.
This operator uses the tensor structure and does not require a
bilinearity assumption on the multiplication of A. -/
def cyclicRowContractionOperator (q : ℕ) [Invertible ((q + 1 : ℕ) : k)] (p : ℕ) :
    chainLevel k A A q ⟶ chainLevel k A A q :=
  ModuleCat.ofHom
    (if Even p then
      -(⅟((q + 1 : ℕ) : k) •
        (∑ i ∈ Finset.range (q + 1), i • TensorPower.consCyclicOperator k A q ^ i))
    else ⅟((q + 1 : ℕ) : k) • 1)

private lemma cyclicContraction_identities (q : ℕ) [Invertible ((q + 1 : ℕ) : k)] :
    let T := TensorPower.consCyclicOperator k A q
    let N := TensorPower.consNorm k A q
    let W := ∑ i ∈ Finset.range (q + 1), i • T ^ i
    let a := ⅟((q + 1 : ℕ) : k)
    ((a • 1) * N + (1 - T) * (-(a • W)) = 1) ∧
      (N * (a • 1) + (-(a • W)) * (1 - T) = 1) := by
  let V := A ⊗[k] TensorPower k q A
  let E := Module.End k V
  let T : E := TensorPower.consCyclicOperator k A q
  let N : E := TensorPower.consNorm k A q
  let W : E := ∑ i ∈ Finset.range (q + 1), i • T ^ i
  let a : k := ⅟((q + 1 : ℕ) : k)
  change ((a • 1) * N + (1 - T) * (-(a • W)) = 1) ∧
    (N * (a • 1) + (-(a • W)) * (1 - T) = 1)
  have ht : T ^ (q + 1) = 1 := TensorPower.consCyclicOperator_period k A q
  have hn : N = ∑ i ∈ Finset.range (q + 1), T ^ i := TensorPower.consNorm_eq_sum k A q
  have hr : W * (1 - T) = N - (q + 1) • (1 : E) := by
    calc
      _ = (∑ i ∈ Finset.range (q + 1), T ^ i) - 1 - q • T ^ (q + 1) :=
        weightedPowerSum_right T q
      _ = N - 1 - q • (1 : E) := by rw [← hn, ht]
      _ = N - (q + 1) • (1 : E) := by
        simp only [add_nsmul, one_nsmul]
        abel
  have hc : T * W = W * T := weightedPowerSum_comm T q
  have hl : (1 - T) * W = N - (q + 1) • (1 : E) := by
    calc
      _ = W * (1 - T) := by rw [sub_mul, one_mul, mul_sub, mul_one, hc]
      _ = _ := hr
  have hd : a • ((q + 1) • (1 : E)) = 1 := by
    change ⅟((q + 1 : ℕ) : k) • ((q + 1) • (1 : E)) = 1
    rw [← Nat.cast_smul_eq_nsmul k (q + 1) (1 : E), smul_smul,
      invOf_mul_self, one_smul]
  have hLeftUnit : (a • (1 : E)) * N = a • N :=
    (smul_mul_assoc a (1 : E) N).trans (congrArg (fun x : E => a • x) (one_mul N))
  have hRightUnit : N * (a • (1 : E)) = a • N :=
    (mul_smul_comm a N (1 : E)).trans (congrArg (fun x : E => a • x) (mul_one N))
  have hLeftProduct : (1 - T) * (-(a • W)) = -(a • (N - (q + 1) • (1 : E))) :=
    (mul_neg (1 - T) (a • W)).trans
      ((congrArg (fun x : E => -x) (mul_smul_comm a (1 - T) W)).trans
        (congrArg (fun x : E => -(a • x)) hl))
  have hRightProduct : (-(a • W)) * (1 - T) = -(a • (N - (q + 1) • (1 : E))) :=
    (neg_mul (a • W) (1 - T)).trans
      ((congrArg (fun x : E => -x) (smul_mul_assoc a W (1 - T))).trans
        (congrArg (fun x : E => -(a • x)) hr))
  have hDifference : a • N + -(a • (N - (q + 1) • (1 : E))) = 1 := by
    calc
      a • N + -(a • (N - (q + 1) • (1 : E))) =
          a • N - a • (N - (q + 1) • (1 : E)) := (sub_eq_add_neg _ _).symm
      _ = a • (N - (N - (q + 1) • (1 : E))) := (smul_sub a N _).symm
      _ = a • ((q + 1) • (1 : E)) :=
        congrArg (fun x : E => a • x) (sub_sub_cancel N ((q + 1) • (1 : E)))
      _ = 1 := hd
  constructor
  · exact (congrArg₂ (fun x y : E => x + y) hLeftUnit hLeftProduct).trans hDifference
  · exact (congrArg₂ (fun x y : E => x + y) hRightUnit hRightProduct).trans hDifference

section Multiplication

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- For a nonunital k-algebra A with k-bilinear multiplication
and q ≥ 0, the qth horizontal cyclic row augments to the chain
complex concentrated in position zero at Cλ_q(A) = coker(1−t_q).
Its position-zero component is the quotient projection, and its
positive-position components are zero. -/
def cyclicRowAugmentation (q : ℕ) :
    (cyclicBicomplex k A).flip.X q ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} k)).obj ((connesComplex k A).X q) := by
  let K := cyclicBicomplex k A
  let L := connesComplex k A
  let R : ChainComplex (ModuleCat.{max u v} k) ℕ := K.flip.X q
  let κ : R.X 0 ⟶ L.X q := (cokernel.π (K.d 1 0)).f q
  refine (ChainComplex.toSingle₀Equiv R (L.X q)).symm ⟨κ, ?_⟩
  have h := congrArg (fun f : K.X 1 ⟶ L => f.f q) (cokernel.condition (K.d 1 0))
  change (K.d 1 0).f q ≫ κ = 0 at h
  exact h

/-- For a nonunital k-algebra A and vertical degree q ≥ 0, the
position-zero component of the horizontal row augmentation is
the projection A ⊗[k] A^⊗q → Cλ_q(A), the evaluated first-column
cokernel projection of the cyclic bicomplex. -/
theorem cyclicRowAugmentation_f_zero (q : ℕ) :
    (cyclicRowAugmentation k A q).f 0 =
      (cokernel.π ((cyclicBicomplex k A).d 1 0)).f q := by
  dsimp only [cyclicRowAugmentation]
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- For a nonunital k-algebra A and q,p ≥ 0, the component of
the qth row augmentation in horizontal position p+1 is zero.
Its target is the single-position complex supported at zero. -/
theorem cyclicRowAugmentation_f_succ (q p : ℕ) :
    (cyclicRowAugmentation k A q).f (p + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
    ((connesComplex k A).X q) (p + 1) (Nat.succ_ne_zero p)).eq_of_tgt _ _

private lemma cyclicRowAugmentation_homotopyEquivalent (q : ℕ)
    [Invertible ((q + 1 : ℕ) : k)] :
    ∃ e : HomotopyEquiv ((cyclicBicomplex k A).flip.X q)
        ((ChainComplex.single₀ (ModuleCat.{max u v} k)).obj ((connesComplex k A).X q)),
      e.hom = cyclicRowAugmentation k A q := by
  let K := cyclicBicomplex k A
  let L := connesComplex k A
  let R : ChainComplex (ModuleCat.{max u v} k) ℕ := K.flip.X q
  let M : ModuleCat.{max u v} k := chainLevel k A A q
  let Q : ModuleCat.{max u v} k := L.X q
  let T : Module.End k M := TensorPower.consCyclicOperator k A q
  let N : Module.End k M := TensorPower.consNorm k A q
  let a : k := ⅟((q + 1 : ℕ) : k)
  let Mean : Module.End k M := a • N
  let μ : M ⟶ M := ModuleCat.ofHom Mean
  let δ : M ⟶ M := (K.d 1 0).f q
  let κ : M ⟶ Q := (cokernel.π (K.d 1 0)).f q
  let H : M ⟶ M := cyclicRowContractionOperator k A q 0
  let H' : M ⟶ M := cyclicRowContractionOperator k A q 1
  have he0 : Even (0 : ℕ) := ⟨0, rfl⟩
  have ho1 : ¬ Even (1 : ℕ) := by decide
  have hδ : δ.hom = 1 - T := connesComplex_levelMap k A q
  have hδMorph : δ = 𝟙 M - cyclicMap k A q := by
    apply ModuleCat.hom_ext
    change δ.hom = (1 : Module.End k M) - T
    exact hδ
  have hδκ : δ ≫ κ = 0 := by
    have h := congrArg (fun f : K.X 1 ⟶ L => f.f q) (cokernel.condition (K.d 1 0))
    change δ ≫ κ = 0 at h
    exact h
  have hEven : normMap k A q ≫ H' + H ≫ δ = 𝟙 M := by
    apply ModuleCat.hom_ext
    change H'.hom * N + δ.hom * H.hom = 1
    rw [hδ]
    simp only [H, H', cyclicRowContractionOperator, ModuleCat.hom_ofHom,
      if_pos he0, if_neg ho1]
    exact (cyclicContraction_identities k A q).1
  have hOdd : δ ≫ H + H' ≫ normMap k A q = 𝟙 M := by
    apply ModuleCat.hom_ext
    change H.hom * δ.hom + N * H'.hom = 1
    rw [hδ]
    simp only [H, H', cyclicRowContractionOperator, ModuleCat.hom_ofHom,
      if_pos he0, if_neg ho1]
    exact (add_comm _ _).trans (cyclicContraction_identities k A q).2
  have hNorm : normMap k A q ≫ H' = μ := by
    apply ModuleCat.hom_ext
    change H'.hom * N = Mean
    simp only [H', cyclicRowContractionOperator, ModuleCat.hom_ofHom, if_neg ho1]
    exact (smul_mul_assoc a (1 : Module.End k M) N).trans
      (congrArg (fun x : Module.End k M => a • x) (one_mul N))
  have hMeanH : μ + H ≫ δ = 𝟙 M := by
    rw [← hNorm]
    exact hEven
  have hMeanκ : μ ≫ κ = κ := by
    have h := congrArg (fun f : M ⟶ M => f ≫ κ) hMeanH
    rw [Preadditive.add_comp, Category.assoc, hδκ, Limits.comp_zero,
      add_zero, Category.id_comp] at h
    exact h
  have hMeanδ : Mean * δ.hom = 0 := by
    rw [hδ]
    change (a • N) * (1 - T) = 0
    rw [smul_mul_assoc, TensorPower.consNorm_mul_one_sub_cyclicOperator, smul_zero]
  let B : Submodule k M := LinearMap.range δ.hom
  have hB : B ≤ LinearMap.ker Mean := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    change Mean (δ.hom y) = 0
    exact DFunLike.congr_fun hMeanδ y
  let S : (M ⧸ B) →ₗ[k] M := B.liftQ Mean hB
  let eQ : Q ≅ ModuleCat.of k (M ⧸ B) := connesComplexXIsoRangeQuotient k A q
  have hκQ : κ ≫ eQ.hom = ModuleCat.ofHom B.mkQ :=
    connesComplex_X_isoRangeQuotient_π k A q
  let γ : Q ⟶ M := eQ.hom ≫ ModuleCat.ofHom S
  have hκγ : κ ≫ γ = μ := by
    calc
      _ = (κ ≫ eQ.hom) ≫ ModuleCat.ofHom S :=
        (Category.assoc κ eQ.hom (ModuleCat.ofHom S)).symm
      _ = ModuleCat.ofHom B.mkQ ≫ ModuleCat.ofHom S := by rw [hκQ]
      _ = μ := by
        apply ModuleCat.hom_ext
        change S.comp B.mkQ = Mean
        exact B.liftQ_mkQ Mean hB
  have hκepi : Epi κ := by
    have hcomp : Epi (κ ≫ eQ.hom) := by
      rw [hκQ]
      exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective B)
    letI : Epi (κ ≫ eQ.hom) := hcomp
    exact (epi_comp_iff_of_isIso κ eQ.hom).mp hcomp
  letI : Epi κ := hκepi
  have hγκ : γ ≫ κ = 𝟙 Q := by
    apply (cancel_epi κ).mp
    rw [Category.comp_id, ← Category.assoc, hκγ, hMeanκ]
  let α : R ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} k)).obj Q :=
    cyclicRowAugmentation k A q
  let β : (ChainComplex.single₀ (ModuleCat.{max u v} k)).obj Q ⟶ R :=
    (ChainComplex.fromSingle₀Equiv R Q).symm γ
  have hα0 : α.f 0 = κ := cyclicRowAugmentation_f_zero k A q
  have hβ0 : β.f 0 = γ := by
    dsimp only [β]
    exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero (C := R) (X := Q)
      (show Q ⟶ R.X 0 from γ)
  have hβα : β ≫ α = 𝟙 _ := by
    apply HomologicalComplex.from_single_hom_ext
    change β.f 0 ≫ α.f 0 = 𝟙 Q
    rw [hβ0, hα0]
    exact hγκ
  let hh : ∀ i j, (ComplexShape.down ℕ).Rel j i → (R.X i ⟶ R.X j) := by
    intro i j _
    exact cyclicRowContractionOperator k A q i
  let Z : R ⟶ R := Homotopy.nullHomotopicMap' hh
  have hz : (Z.f 0 : M ⟶ M) = H ≫ δ :=
    Homotopy.nullHomotopicMap'_f_of_not_rel_left
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
      (by intro i; simp [ComplexShape.down_Rel]) hh
  have hOp (p : ℕ) : cyclicRowContractionOperator k A q p =
      if Even p then H else H' := by
    by_cases hp : Even p
    · simp only [cyclicRowContractionOperator, if_pos hp, H, if_pos he0]
    · simp only [cyclicRowContractionOperator, if_neg hp, H', if_neg ho1]
  have hs (p : ℕ) : (Z.f (p + 1) : M ⟶ M) =
      (if Even p then δ else normMap k A q) ≫
          (if Even p then H else H') +
        (if Even (p + 1) then H else H') ≫
          (if Even (p + 1) then δ else normMap k A q) := by
    have h := Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel (p + 2) (p + 1) from rfl)
      (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) hh
    let dOut : M ⟶ M := R.d (p + 1) p
    let dIn : M ⟶ M := R.d (p + 2) (p + 1)
    let hOutOp : M ⟶ M := cyclicRowContractionOperator k A q p
    let hInOp : M ⟶ M := cyclicRowContractionOperator k A q (p + 1)
    change (Z.f (p + 1) : M ⟶ M) = dOut ≫ hOutOp + hInOp ≫ dIn at h
    have hOut : (R.d (p + 1) p : M ⟶ M) = if Even p then δ else normMap k A q := by
      have h : (R.d (p + 1) p : M ⟶ M) =
          if Even p then 𝟙 M - cyclicMap k A q else normMap k A q :=
        cyclicBicomplex_horizontal k A p q
      exact h.trans (congrArg
        (fun d : M ⟶ M => if Even p then d else normMap k A q) hδMorph.symm)
    have hIn : (R.d (p + 2) (p + 1) : M ⟶ M) =
        if Even (p + 1) then δ else normMap k A q := by
      have h : (R.d (p + 2) (p + 1) : M ⟶ M) =
          if Even (p + 1) then 𝟙 M - cyclicMap k A q else normMap k A q :=
        cyclicBicomplex_horizontal k A (p + 1) q
      exact h.trans (congrArg
        (fun d : M ⟶ M => if Even (p + 1) then d else normMap k A q) hδMorph.symm)
    have hdOut : dOut = if Even p then δ else normMap k A q := hOut
    have hdIn : dIn = if Even (p + 1) then δ else normMap k A q := hIn
    have hhOut : hOutOp = if Even p then H else H' := hOp p
    have hhIn : hInOp = if Even (p + 1) then H else H' := hOp (p + 1)
    exact h.trans (congrArg₂ (fun x y : M ⟶ M => x + y)
      (congrArg₂ (fun x y : M ⟶ M => x ≫ y) hdOut hhOut)
      (congrArg₂ (fun x y : M ⟶ M => x ≫ y) hhIn hdIn))
  have hDiff : 𝟙 R - α ≫ β = Z := by
    apply HomologicalComplex.hom_ext
    intro p
    cases p with
    | zero =>
        let α₀ : M ⟶ Q := α.f 0
        let β₀ : Q ⟶ M := β.f 0
        have hα₀ : α₀ = κ := hα0
        have hβ₀ : β₀ = γ := hβ0
        have hComposite : α₀ ≫ β₀ = μ :=
          (congrArg₂ (fun (f : M ⟶ Q) (g : Q ⟶ M) => f ≫ g) hα₀ hβ₀).trans hκγ
        change 𝟙 M - α₀ ≫ β₀ = (Z.f 0 : M ⟶ M)
        rw [hComposite, hz]
        apply sub_eq_iff_eq_add.mpr
        exact hMeanH.symm.trans (add_comm μ (H ≫ δ))
    | succ p =>
        let Qp := ((ChainComplex.single₀ (ModuleCat.{max u v} k)).obj Q).X (p + 1)
        let αp : M ⟶ Qp := α.f (p + 1)
        let βp : Qp ⟶ M := β.f (p + 1)
        have hαp : αp = 0 := cyclicRowAugmentation_f_succ k A q p
        have hComposite : αp ≫ βp = 0 :=
          (congrArg (fun f : M ⟶ Qp => f ≫ βp) hαp).trans (Limits.zero_comp (f := βp))
        change 𝟙 M - αp ≫ βp = (Z.f (p + 1) : M ⟶ M)
        rw [hComposite, sub_zero, hs p]
        by_cases hp : Even p
        · have hp' : ¬ Even (p + 1) := by
            simpa only [Nat.even_add_one, not_not] using hp
          simp only [if_pos hp, if_neg hp']
          exact hOdd.symm
        · have hp' : Even (p + 1) := Nat.even_add_one.mpr hp
          simp only [if_neg hp, if_pos hp']
          exact hEven.symm
  let hId : Homotopy (𝟙 R) (α ≫ β) :=
    (Homotopy.equivSubZero (f := 𝟙 R) (g := α ≫ β)).symm
      ((Homotopy.ofEq hDiff).trans (Homotopy.nullHomotopy' hh))
  let e : HomotopyEquiv R ((ChainComplex.single₀ (ModuleCat.{max u v} k)).obj Q) :=
    { hom := α
      inv := β
      homotopyHomInvId := hId.symm
      homotopyInvHomId := Homotopy.ofEq hβα }
  exact ⟨e, rfl⟩

/-- For a nonunital k-algebra A with k-bilinear multiplication
and q ≥ 0, if q+1 is invertible in k, the augmentation of the qth
horizontal cyclic row to Cλ_q(A) concentrated in position zero
is a quasi-isomorphism. Only this single integer q+1 is required
to be invertible; k need not be a ℚ-algebra. -/
theorem cyclicRowAugmentation_quasiIso (q : ℕ) [Invertible ((q + 1 : ℕ) : k)] :
    QuasiIso (cyclicRowAugmentation k A q) := by
  obtain ⟨e, he⟩ := cyclicRowAugmentation_homotopyEquivalent k A q
  rw [← he]
  infer_instance

/-- For a nonunital k-algebra A with k-bilinear multiplication,
the horizontal row augmentations form a map from the transposed cyclic
bicomplex to the bicomplex whose row in outer degree q is concentrated
at horizontal position zero with value Cλ_q(A).
The outer differential is induced by the Connes quotient differential. -/
def cyclicConnesAugmentation :
    (cyclicBicomplex k A).flip ⟶
      HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj (connesComplex k A) :=
  ChainComplex.ofHom (fun q => cyclicRowAugmentation k A q) fun q => by
    apply HomologicalComplex.to_single_hom_ext
    change (cyclicRowAugmentation k A (q + 1)).f 0 ≫
        ((ChainComplex.single₀ (ModuleCat.{max u v} k)).map
          ((connesComplex k A).d (q + 1) q)).f 0 =
      ((cyclicBicomplex k A).flip.d (q + 1) q).f 0 ≫
        (cyclicRowAugmentation k A q).f 0
    rw [cyclicRowAugmentation_f_zero, cyclicRowAugmentation_f_zero]
    change (cokernel.π ((cyclicBicomplex k A).d 1 0)).f (q + 1) ≫
        (connesComplex k A).d (q + 1) q =
      ((cyclicBicomplex k A).X 0).d (q + 1) q ≫
        (cokernel.π ((cyclicBicomplex k A).d 1 0)).f q
    exact (cokernel.π ((cyclicBicomplex k A).d 1 0)).comm (q + 1) q

/-- For a nonunital k-algebra A and q ≥ 0, the outer degree-q
component of the bicomplex Connes augmentation is the horizontal
row augmentation to Cλ_q(A) concentrated in position zero. -/
theorem cyclicConnesAugmentation_f (q : ℕ) :
    (cyclicConnesAugmentation k A).f q = cyclicRowAugmentation k A q := rfl

/-- For a nonunital k-algebra A with k-bilinear multiplication,
the cyclic-to-Connes chain map equals the inverse total-transposition
isomorphism followed by the total augmentation of the horizontal
row map. The transposition carries sign (−1)^(pq).
On an antidiagonal summand (p,q), the map is the quotient projection
when p = 0 and zero when p > 0. -/
theorem cyclicToConnes_eq_transposedAugmentation :
    cyclicToConnes k A =
      ((cyclicBicomplex k A).totalFlipIso (ComplexShape.down ℕ)).inv ≫
        HomologicalComplex₂.totalAugmentationDownNat (cyclicConnesAugmentation k A) := by
  let K := cyclicBicomplex k A
  let L := connesComplex k A
  let φ := cyclicConnesAugmentation k A
  let a : K.flip.total (ComplexShape.down ℕ) ⟶ L :=
    HomologicalComplex₂.totalAugmentationDownNat φ
  let e := K.totalFlipIso (ComplexShape.down ℕ)
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change K.ιTotal (ComplexShape.down ℕ) p q n h ≫ (cyclicToConnes k A).f n =
    K.ιTotal (ComplexShape.down ℕ) p q n h ≫ (e.inv.f n ≫ a.f n)
  have hFlip := HomologicalComplex₂.ιTotal_totalFlipIso_f_inv
    (K := K) (c := ComplexShape.down ℕ) p q n h
  erw [← Category.assoc, hFlip, Linear.units_smul_comp]
  cases p with
  | zero =>
      have hq : q = n := by
        change 0 + q = n at h
        simpa only [Nat.zero_add] using h
      subst q
      rw [cyclicToConnes_ι_zero]
      have hσ : ComplexShape.σ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) 0 n = 1 := by
        rw [HomologicalComplex.ComplexShape.σ_down_ℕ, Nat.zero_mul, pow_zero]
      dsimp only [a, φ]
      erw [hσ, one_smul,
        HomologicalComplex₂.ιTotal_comp_totalAugmentationDownNat_zero,
        cyclicConnesAugmentation_f, cyclicRowAugmentation_f_zero] <;>
        exact (Category.comp_id _).symm
  | succ p =>
      rw [cyclicToConnes_ι_succ]
      dsimp only [a, φ]
      erw [HomologicalComplex₂.ιTotal_comp_totalAugmentationDownNat,
        cyclicConnesAugmentation_f, cyclicRowAugmentation_f_succ] <;>
        simp only [Limits.zero_comp]
      change (0 : chainLevel k A A q ⟶ L.X n) =
        (ComplexShape.down ℕ).σ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p + 1) q • (0 : chainLevel k A A q ⟶ L.X n)
      exact (smul_zero _).symm

section Rational

variable [Algebra ℚ k]

/-- For a commutative ℚ-algebra k and a nonunital k-algebra A
with k-bilinear multiplication, the chain map from the cyclic total
to the Connes quotient complex is a quasi-isomorphism.
It is the first-column quotient projection in column zero and
vanishes on all positive columns. -/
instance cyclicToConnesQuasiIso : QuasiIso (cyclicToConnes k A) := by
  let K := cyclicBicomplex k A
  let L := connesComplex k A
  let φ := cyclicConnesAugmentation k A
  have hRows : ∀ q : ℕ, QuasiIso (φ.f q) := by
    intro q
    have hq : ((q + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero q)
    letI : Invertible ((q + 1 : ℕ) : ℚ) := invertibleOfNonzero hq
    letI : Invertible ((q + 1 : ℕ) : k) := by
      simpa only [map_natCast] using
        (Invertible.map (algebraMap ℚ k) ((q + 1 : ℕ) : ℚ))
    change QuasiIso (cyclicRowAugmentation k A q)
    exact cyclicRowAugmentation_quasiIso k A q
  have hTotal : QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant φ hRows
  letI : QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) := hTotal
  have hAug : QuasiIso (HomologicalComplex₂.totalAugmentationDownNat φ) := by
    change QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) ≫
      (HomologicalComplex₂.single₀MapTotalIso L).hom)
    infer_instance
  letI : QuasiIso (HomologicalComplex₂.totalAugmentationDownNat φ) := hAug
  have hComp : QuasiIso ((K.totalFlipIso (ComplexShape.down ℕ)).inv ≫
      HomologicalComplex₂.totalAugmentationDownNat φ) := inferInstance
  rw [← cyclicToConnes_eq_transposedAugmentation k A] at hComp
  exact hComp

/-- For a commutative ℚ-algebra k, a nonunital k-algebra A with
k-bilinear multiplication and every n ≥ 0, the map
HC_n(A) → H_n(Cλ(A)) induced by the first-column projection is an
isomorphism of k-modules. -/
instance cyclicToConnesHomologyIsIso (n : ℕ) :
    IsIso (cyclicToConnesHomology k A n) := by
  change IsIso (HomologicalComplex.homologyMap (cyclicToConnes k A) n)
  infer_instance

/-- For a commutative ℚ-algebra k and a nonunital k-algebra A
with k-bilinear multiplication, the first-column projection induces
the k-module isomorphism HC_n(A) ≅ H_n(Cλ(A)) for each n ≥ 0.
Both homology objects lie in ModuleCat^max(u,v)(k), with independent
carrier worlds u and v of k and A. -/
def cyclicToConnesHomologyIso (n : ℕ) : cyclicHomology k A n ≅ connesHomology k A n :=
  asIso (cyclicToConnesHomology k A n)

/-- For a commutative ℚ-algebra k, a nonunital k-algebra A with
k-bilinear multiplication and n ≥ 0, the forward morphism of
HC_n(A) ≅ H_n(Cλ(A)) is precisely the homology map of the
first-column cyclic-to-Connes projection. -/
theorem cyclicToConnesHomologyIso_hom (n : ℕ) :
    (cyclicToConnesHomologyIso k A n).hom = cyclicToConnesHomology k A n := rfl

variable {A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- For nonunital k-algebras A and B in the same carrier world,
a nonunital k-algebra map f : A → B, k a commutative ℚ-algebra and
n ≥ 0, the inverse comparison maps χ_A⁻¹ and χ_B⁻¹ satisfy
χ_B⁻¹ ∘ H_n(Cλ(f)) = HC_n(f) ∘ χ_A⁻¹.
This is a square from H_n(Cλ(A)) to HC_n(B). -/
theorem cyclicToConnesHomologyIso_inv_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    connesHomologyMap f n ≫ (cyclicToConnesHomologyIso k B n).inv =
      (cyclicToConnesHomologyIso k A n).inv ≫ cyclicHomologyMap f n := by
  let eA := cyclicToConnesHomologyIso k A n
  let eB := cyclicToConnesHomologyIso k B n
  have h : cyclicHomologyMap f n ≫ eB.hom = eA.hom ≫ connesHomologyMap f n :=
    cyclicToConnesHomology_naturality f n
  apply (cancel_mono eB.hom).mp
  rw [Category.assoc, eB.inv_hom_id, Category.comp_id, Category.assoc, h,
    ← Category.assoc, eA.inv_hom_id, Category.id_comp]

end Rational

end Multiplication

end ModuleCat.Algebra.Hochschild.NonUnital
