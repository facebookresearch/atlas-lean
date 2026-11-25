/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement
public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeRowCore
public import MathlibExt.CategoryTheory.ExactCategory.ExactFunctor

/-!
# A finite-idempotent exact model of finitely generated projectives

Natural-rank tuples of the single-object opposite ring give a standard Karoubi
model of all finitely generated projective left modules. Its actual row-range
realization is a split-exact equivalence. The specified free, zero, regular and
biproduct comparisons preserve arbitrary matrices, full opposite general-linear
blocks and regular stabilization over every ring, including zero rings.
-/

noncomputable section

open CategoryTheory Limits
open scoped Matrix

universe u

namespace FGProjectiveCat

variable (A : Type u) [Ring A]

private abbrev RowTuple := Mat_ (SingleObj Aᵐᵒᵖ)

private abbrev rankTuple (n : ℕ) : RowTuple A where
  ι := Fin n
  X _ := Quiver.SingleObj.star Aᵐᵒᵖ

private abbrev RankBase := InducedCategory (RowTuple A) (rankTuple A)

private def rankInclusion : RankBase A ⥤ RowTuple A :=
  inducedFunctor (rankTuple A)

private def rankTupleIso (M : RowTuple A) :
    rankTuple A (Fintype.card M.ι) ≅ M := by
  classical
  let e := Fintype.equivFin M.ι
  let forward : rankTuple A (Fintype.card M.ι) ⟶ M :=
    fun i j => if e j = i then (1 : Aᵐᵒᵖ) else 0
  let backward : M ⟶ rankTuple A (Fintype.card M.ι) :=
    fun i j => if e i = j then (1 : Aᵐᵒᵖ) else 0
  refine
    { hom := forward
      inv := backward
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Mat_.hom_ext
    intro i j
    by_cases hij : i = j
    · subst j
      rw [Mat_.comp_apply, Mat_.id_apply_self, SingleObj.id_as_one]
      change (∑ k : M.ι, (if e k = i then (1 : Aᵐᵒᵖ) else 0) *
        (if e k = i then 1 else 0)) = 1
      rw [Finset.sum_eq_single (e.symm i)]
      · simp
      · intro k _ hk
        have hki : e k ≠ i := by
          intro h
          apply hk
          simpa using congrArg e.symm h
        simp [hki]
      · simp
    · rw [Mat_.comp_apply, Mat_.id_apply_of_ne _ _ _ hij]
      change (∑ k : M.ι, (if e k = j then (1 : Aᵐᵒᵖ) else 0) *
        (if e k = i then 1 else 0)) = 0
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : e k = i
      · simp [hki, hij]
      · simp [hki]
  · apply Mat_.hom_ext
    intro i j
    by_cases hij : i = j
    · subst j
      rw [Mat_.id_apply_self]
      rw [SingleObj.id_as_one, Mat_.comp_apply]
      change (∑ k : Fin (Fintype.card M.ι),
        (if e i = k then (1 : Aᵐᵒᵖ) else 0) *
        (if e i = k then 1 else 0)) = 1
      rw [Finset.sum_eq_single (e i)]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    · rw [Mat_.id_apply_of_ne _ _ _ hij]
      rw [Mat_.comp_apply]
      change (∑ k : Fin (Fintype.card M.ι),
        (if e j = k then (1 : Aᵐᵒᵖ) else 0) *
        (if e i = k then 1 else 0)) = 0
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : e i = k
      · have hkj : e j ≠ k := by
          intro h
          exact hij (e.injective (hki.trans h.symm))
        simp [hki, hkj]
      · simp [hki]

private instance rankInclusionIsEquivalence : (rankInclusion A).IsEquivalence where
  faithful := (fullyFaithfulInducedFunctor (rankTuple A)).faithful
  full := (fullyFaithfulInducedFunctor (rankTuple A)).full
  essSurj := ⟨fun M => ⟨Fintype.card M.ι, ⟨rankTupleIso A M⟩⟩⟩

private def rankEquivalence : RankBase A ≌ RowTuple A :=
  (rankInclusion A).asEquivalence

private instance rankBaseHasFiniteProducts : HasFiniteProducts (RankBase A) where
  out n := Adjunction.hasLimitsOfShape_of_equivalence
    (J := Discrete (Fin n)) (rankInclusion A)

private instance rankBaseHasFiniteBiproducts : HasFiniteBiproducts (RankBase A) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private instance rankInclusionAdditive : (rankInclusion A).Additive where
  map_add {X Y} {f g} :=
    (InducedCategory.homAddEquiv (X := X) (Y := Y)).map_add f g

private instance rankEquivalenceFunctorAdditive : (rankEquivalence A).functor.Additive := by
  change (rankInclusion A).Additive
  infer_instance

private instance rankEquivalenceInverseAdditive : (rankEquivalence A).inverse.Additive :=
  Equivalence.inverse_additive (rankEquivalence A)

private def rowMatrix {n m : RankBase A} (f : n ⟶ m) : Matrix (Fin n) (Fin m) A :=
  fun i j => MulOpposite.unop (f.hom i j)

private def rowMatrixHom {n m : RankBase A} (a : Matrix (Fin n) (Fin m) A) : n ⟶ m :=
  InducedCategory.homMk (fun i j => MulOpposite.op (a i j))

private theorem rowMatrix_rowMatrixHom {n m : RankBase A}
    (a : Matrix (Fin n) (Fin m) A) : rowMatrix A (rowMatrixHom A a) = a := by
  ext i j
  rfl

private theorem rowMatrixHom_rowMatrix {n m : RankBase A} (f : n ⟶ m) :
    rowMatrixHom A (rowMatrix A f) = f := by
  apply InducedCategory.hom_ext
  funext i j
  rfl

private theorem rowMatrix_comp {n m k : RankBase A} (f : n ⟶ m) (g : m ⟶ k) :
    rowMatrix A (f ≫ g) = rowMatrix A f * rowMatrix A g := by
  ext i j
  change MulOpposite.unop
      (∑ l : Fin m, (show Aᵐᵒᵖ from g.hom l j) * (show Aᵐᵒᵖ from f.hom i l)) =
    ∑ l : Fin m, MulOpposite.unop (f.hom i l) * MulOpposite.unop (g.hom l j)
  simp only [Finset.unop_sum, MulOpposite.unop_mul]

private theorem rowMatrix_id (n : RankBase A) : rowMatrix A (𝟙 n) = 1 := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    change MulOpposite.unop ((𝟙 (rankTuple A n)) i i) = _
    rw [Mat_.id_apply_self]
    change (1 : A) = (1 : Matrix (Fin n) (Fin n) A) i i
    simp
  · change MulOpposite.unop ((𝟙 (rankTuple A n)) i j) = _
    rw [Mat_.id_apply_of_ne _ _ _ h]
    simp [h]

private theorem rowMatrix_add {n m : RankBase A} (f g : n ⟶ m) :
    rowMatrix A (f + g) = rowMatrix A f + rowMatrix A g := by
  ext i j
  change MulOpposite.unop (f.hom i j + g.hom i j) = _
  rfl

private def freeRow : RankBase A ⥤ FGProjectiveCat.{u} A where
  obj n := standardFree A n
  map f := ofHom (rowMatrix A f).toLinearMapRight'
  map_id n := by
    apply FGProjectiveCat.hom_ext
    change (rowMatrix A (𝟙 n)).toLinearMapRight' = LinearMap.id
    rw [rowMatrix_id, Matrix.toLinearMapRight'_one]
  map_comp f g := by
    apply FGProjectiveCat.hom_ext
    change (rowMatrix A (f ≫ g)).toLinearMapRight' =
      (rowMatrix A g).toLinearMapRight'.comp (rowMatrix A f).toLinearMapRight'
    rw [rowMatrix_comp, Matrix.toLinearMapRight'_mul]

private instance freeRowAdditive : (freeRow A).Additive where
  map_add {X Y} {f g} := by
    apply FGProjectiveCat.hom_ext
    change (rowMatrix A (f + g)).toLinearMapRight' =
      (rowMatrix A f).toLinearMapRight' + (rowMatrix A g).toLinearMapRight'
    rw [rowMatrix_add]
    exact Matrix.toLinearMapRight'.map_add _ _

private def freeRowFullyFaithful : (freeRow A).FullyFaithful where
  preimage f := rowMatrixHom A f.hom.hom.toMatrixRight'
  map_preimage f := by
    apply FGProjectiveCat.hom_ext
    change (rowMatrix A (rowMatrixHom A f.hom.hom.toMatrixRight')).toLinearMapRight' =
      f.hom.hom
    rw [rowMatrix_rowMatrixHom]
    exact LinearMap.toMatrixRight'.symm_apply_apply _
  preimage_map f := by
    change rowMatrixHom A (rowMatrix A f).toLinearMapRight'.toMatrixRight' = f
    rw [LinearMap.toMatrixRight'.apply_symm_apply]
    exact rowMatrixHom_rowMatrix A f

private abbrev IdempotentRows := Idempotents.Karoubi (RankBase A)

private instance idempotentRowsHasFiniteBiproducts : HasFiniteBiproducts (IdempotentRows A) := by
  infer_instance

private instance idempotentRowsHasBinaryBiproducts : HasBinaryBiproducts (IdempotentRows A) :=
  hasBinaryBiproducts_of_finite_biproducts (IdempotentRows A)

private instance idempotentRowsSplitExact : ExactCategory (IdempotentRows A) :=
  ExactCategory.splitExactCategory

private theorem rowMatrix_idempotent (P : IdempotentRows A) :
    rowMatrix A P.p * rowMatrix A P.p = rowMatrix A P.p :=
  (rowMatrix_comp A P.p P.p).symm.trans (congrArg (rowMatrix A) P.idem)

private theorem rowRangeFixed {n : ℕ} (e : Matrix (Fin n) (Fin n) A) (he : e * e = e)
    (x : LinearMap.range e.toLinearMapRight') :
    e.toLinearMapRight' x.1 = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  rw [← hy, ← Matrix.toLinearMapRight'_mul_apply, he]

private theorem rowRangeSplit {n : ℕ} (e : Matrix (Fin n) (Fin n) A) (he : e * e = e) :
    e.toLinearMapRight'.rangeRestrict.comp (LinearMap.range e.toLinearMapRight').subtype =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact rowRangeFixed A e he x

private theorem rowRangeFinite {n : ℕ} (e : Matrix (Fin n) (Fin n) A) :
    Module.Finite A (LinearMap.range e.toLinearMapRight') :=
  Module.Finite.of_surjective e.toLinearMapRight'.rangeRestrict
    e.toLinearMapRight'.surjective_rangeRestrict

private theorem rowRangeProjective {n : ℕ} (e : Matrix (Fin n) (Fin n) A) (he : e * e = e) :
    Module.Projective A (LinearMap.range e.toLinearMapRight') :=
  Module.Projective.of_split (LinearMap.range e.toLinearMapRight').subtype
    e.toLinearMapRight'.rangeRestrict (rowRangeSplit A e he)

private abbrev rowRange (P : IdempotentRows A) : Submodule A (Fin P.X → A) :=
  LinearMap.range (rowMatrix A P.p).toLinearMapRight'

private instance rowRangeFiniteInstance (P : IdempotentRows A) : Module.Finite A (rowRange A P) :=
  rowRangeFinite A (rowMatrix A P.p)

private instance rowRangeProjectiveInstance (P : IdempotentRows A) :
    Module.Projective A (rowRange A P) :=
  rowRangeProjective A (rowMatrix A P.p) (rowMatrix_idempotent A P)

private abbrev rowObject (P : IdempotentRows A) : FGProjectiveCat.{u} A :=
  FGProjectiveCat.of (R := A) (rowRange A P)

private theorem rowCorner_left {P Q : IdempotentRows A} (f : P ⟶ Q) :
    rowMatrix A P.p * rowMatrix A f.f = rowMatrix A f.f :=
  (rowMatrix_comp A P.p f.f).symm.trans
    (congrArg (rowMatrix A) (Idempotents.Karoubi.p_comp f))

private theorem rowCorner_right {P Q : IdempotentRows A} (f : P ⟶ Q) :
    rowMatrix A f.f * rowMatrix A Q.p = rowMatrix A f.f :=
  (rowMatrix_comp A f.f Q.p).symm.trans
    (congrArg (rowMatrix A) (Idempotents.Karoubi.comp_p f))

private def rowCornerLinear {P Q : IdempotentRows A} (f : P ⟶ Q) :
    rowRange A P →ₗ[A] rowRange A Q :=
  LinearMap.codRestrict (rowRange A Q)
    ((rowMatrix A f.f).toLinearMapRight'.comp (rowRange A P).subtype) (by
      intro x
      refine ⟨(rowMatrix A f.f).toLinearMapRight' x.1, ?_⟩
      change (rowMatrix A Q.p).toLinearMapRight'
          ((rowMatrix A f.f).toLinearMapRight' x.1) =
        (rowMatrix A f.f).toLinearMapRight' x.1
      rw [← Matrix.toLinearMapRight'_mul_apply, rowCorner_right])

private def realization : IdempotentRows A ⥤ FGProjectiveCat.{u} A where
  obj P := rowObject A P
  map f := FGProjectiveCat.ofHom (rowCornerLinear A f)
  map_id P := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (rowMatrix A P.p).toLinearMapRight' x.1 = x.1
    exact rowRangeFixed A (rowMatrix A P.p) (rowMatrix_idempotent A P) x
  map_comp f g := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (rowMatrix A (f ≫ g).f).toLinearMapRight' x.1 =
      (rowMatrix A g.f).toLinearMapRight' ((rowMatrix A f.f).toLinearMapRight' x.1)
    rw [Idempotents.Karoubi.comp_f, rowMatrix_comp, Matrix.toLinearMapRight'_mul_apply]

private instance realizationAdditive : (realization A).Additive where
  map_add {P Q} {f g} := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (rowMatrix A (f.f + g.f)).toLinearMapRight' x.1 =
      (rowMatrix A f.f).toLinearMapRight' x.1 + (rowMatrix A g.f).toLinearMapRight' x.1
    rw [rowMatrix_add]
    exact LinearMap.congr_fun (Matrix.toLinearMapRight'.map_add _ _) x.1

private theorem rowMatrix_injective {n m : RankBase A} :
    Function.Injective (rowMatrix A (n := n) (m := m)) := by
  intro f g h
  calc
    f = rowMatrixHom A (rowMatrix A f) := (rowMatrixHom_rowMatrix A f).symm
    _ = rowMatrixHom A (rowMatrix A g) := congrArg (rowMatrixHom A) h
    _ = g := rowMatrixHom_rowMatrix A g

private def rowExtension {P Q : IdempotentRows A}
    (L : rowRange A P →ₗ[A] rowRange A Q) : (Fin P.X → A) →ₗ[A] (Fin Q.X → A) :=
  (rowRange A Q).subtype.comp (L.comp (rowMatrix A P.p).toLinearMapRight'.rangeRestrict)

private theorem rowExtension_pre {P Q : IdempotentRows A}
    (L : rowRange A P →ₗ[A] rowRange A Q) :
    (rowExtension A L).comp (rowMatrix A P.p).toLinearMapRight' = rowExtension A L := by
  apply LinearMap.ext
  intro x
  have hP : (rowMatrix A P.p).toLinearMapRight'.rangeRestrict
        ((rowMatrix A P.p).toLinearMapRight' x) =
      (rowMatrix A P.p).toLinearMapRight'.rangeRestrict x := by
    apply Subtype.ext
    change (rowMatrix A P.p).toLinearMapRight' ((rowMatrix A P.p).toLinearMapRight' x) =
      (rowMatrix A P.p).toLinearMapRight' x
    rw [← Matrix.toLinearMapRight'_mul_apply, rowMatrix_idempotent]
  exact congrArg (fun y => (L y).1) hP

private theorem rowExtension_post {P Q : IdempotentRows A}
    (L : rowRange A P →ₗ[A] rowRange A Q) :
    (rowMatrix A Q.p).toLinearMapRight'.comp (rowExtension A L) = rowExtension A L := by
  apply LinearMap.ext
  intro x
  exact rowRangeFixed A (rowMatrix A Q.p) (rowMatrix_idempotent A Q)
    (L ((rowMatrix A P.p).toLinearMapRight'.rangeRestrict x))

private theorem rowExtension_matrix_left {P Q : IdempotentRows A}
    (L : rowRange A P →ₗ[A] rowRange A Q) :
    rowMatrix A P.p * (rowExtension A L).toMatrixRight' = (rowExtension A L).toMatrixRight' := by
  have h := congrArg (fun f => f.toMatrixRight') (rowExtension_pre A L)
  simpa only [LinearMap.toMatrixRight'_comp, LinearMap.toMatrixRight'.apply_symm_apply] using h

private theorem rowExtension_matrix_right {P Q : IdempotentRows A}
    (L : rowRange A P →ₗ[A] rowRange A Q) :
    (rowExtension A L).toMatrixRight' * rowMatrix A Q.p = (rowExtension A L).toMatrixRight' := by
  have h := congrArg (fun f => f.toMatrixRight') (rowExtension_post A L)
  simpa only [LinearMap.toMatrixRight'_comp, LinearMap.toMatrixRight'.apply_symm_apply] using h

private def rowCornerPreimage {P Q : IdempotentRows A}
    (L : rowRange A P →ₗ[A] rowRange A Q) : P ⟶ Q where
  f := rowMatrixHom A (rowExtension A L).toMatrixRight'
  comm := by
    apply rowMatrix_injective A
    rw [rowMatrix_comp, rowMatrix_comp, rowMatrix_rowMatrixHom]
    rw [rowExtension_matrix_right, rowExtension_matrix_left]

private theorem rowExtension_corner {P Q : IdempotentRows A} (f : P ⟶ Q) :
    rowExtension A (rowCornerLinear A f) = (rowMatrix A f.f).toLinearMapRight' := by
  apply LinearMap.ext
  intro x
  change (rowMatrix A f.f).toLinearMapRight' ((rowMatrix A P.p).toLinearMapRight' x) =
    (rowMatrix A f.f).toLinearMapRight' x
  rw [← Matrix.toLinearMapRight'_mul_apply, rowCorner_left]

private def realizationFullyFaithful : (realization A).FullyFaithful where
  preimage f := rowCornerPreimage A f.hom.hom
  map_preimage {P Q} f := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (rowMatrix A (rowMatrixHom A
        (rowExtension A f.hom.hom).toMatrixRight')).toLinearMapRight' x.1 = (f.hom.hom x).1
    rw [rowMatrix_rowMatrixHom, LinearMap.toMatrixRight'.symm_apply_apply]
    have h := LinearMap.congr_fun
      (rowRangeSplit A (rowMatrix A P.p) (rowMatrix_idempotent A P)) x
    change (rowMatrix A P.p).toLinearMapRight'.rangeRestrict x.1 = x at h
    exact congrArg (fun y => (f.hom.hom y).1) h
  preimage_map {P Q} f := by
    apply Idempotents.Karoubi.Hom.ext
    apply rowMatrix_injective A
    change rowMatrix A (rowMatrixHom A (rowExtension A (rowCornerLinear A f)).toMatrixRight') =
      rowMatrix A f.f
    rw [rowMatrix_rowMatrixHom, rowExtension_corner, LinearMap.toMatrixRight'.apply_symm_apply]

private theorem realizationEssSurj (P : FGProjectiveCat.{u} A) :
    ∃ X : IdempotentRows A, Nonempty ((realization A).obj X ≅ P) := by
  classical
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let e := (g.comp f).toMatrixRight'
  have hq : (g.comp f).comp (g.comp f) = g.comp f := by
    apply LinearMap.ext
    intro x
    change g (f (g (f x))) = g (f x)
    exact congrArg g (LinearMap.congr_fun hfg (f x))
  have he : e * e = e := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul]
    simpa only [e, LinearMap.toMatrixRight'.symm_apply_apply] using hq
  let X : IdempotentRows A :=
    { X := n
      p := rowMatrixHom A e
      idem := by
        apply rowMatrix_injective A
        rw [rowMatrix_comp, rowMatrix_rowMatrixHom]
        exact he }
  have hX : (rowMatrix A X.p).toLinearMapRight' = g.comp f := by
    change (rowMatrix A (rowMatrixHom A e)).toLinearMapRight' = g.comp f
    rw [rowMatrix_rowMatrixHom]
    exact LinearMap.toMatrixRight'.symm_apply_apply (g.comp f)
  let toP : rowRange A X →ₗ[A] P := f.comp (rowRange A X).subtype
  let fromP : P →ₗ[A] rowRange A X :=
    LinearMap.codRestrict (rowRange A X) g (by
      intro x
      refine ⟨g x, ?_⟩
      change (rowMatrix A X.p).toLinearMapRight' (g x) = g x
      rw [hX]
      exact congrArg g (LinearMap.congr_fun hfg x))
  have h_to_from : toP.comp fromP = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change f (g x) = x
    exact LinearMap.congr_fun hfg x
  have h_from_to : fromP.comp toP = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (g.comp f) x.1 = x.1
    rw [← hX]
    exact rowRangeFixed A (rowMatrix A X.p) (rowMatrix_idempotent A X) x
  let i : (realization A).obj X ≅ P :=
    FGProjectiveCat.isoOfLinearEquiv (LinearEquiv.ofLinearMap toP fromP h_to_from h_from_to)
  exact ⟨X, ⟨i⟩⟩

private instance realizationIsEquivalence : (realization A).IsEquivalence where
  faithful := (realizationFullyFaithful A).faithful
  full := (realizationFullyFaithful A).full
  essSurj := ⟨realizationEssSurj A⟩

private def projectiveEquivalence : IdempotentRows A ≌ FGProjectiveCat.{u} A :=
  (realization A).asEquivalence

private instance projectiveEquivalenceFunctorAdditive :
    (projectiveEquivalence A).functor.Additive := by
  change (realization A).Additive
  infer_instance

private instance projectiveEquivalenceInverseAdditive :
    (projectiveEquivalence A).inverse.Additive :=
  Equivalence.inverse_additive (projectiveEquivalence A)

private instance projectiveEquivalenceFunctorExact : (projectiveEquivalence A).functor.IsExact := by
  change (realization A).IsExact
  exact ExactCategory.isExact_splitSource (realization A)

private instance projectiveEquivalenceInverseExact : (projectiveEquivalence A).inverse.IsExact :=
  ExactCategory.isExact_splitSource (projectiveEquivalence A).inverse

open scoped ZeroObject

private abbrev freeObject (n : ℕ) : IdempotentRows A :=
  (Idempotents.toKaroubi (RankBase A)).obj n

private theorem freeObject_matrix (n : ℕ) : rowMatrix A (freeObject A n).p = 1 :=
  rowMatrix_id A n

private def freeIso (n : ℕ) :
    (projectiveEquivalence A).functor.obj (freeObject A n) ≅ standardFree A n := by
  let X := freeObject A n
  let forward : rowRange A X →ₗ[A] (Fin n → A) := (rowRange A X).subtype
  let backward : (Fin n → A) →ₗ[A] rowRange A X :=
    LinearMap.codRestrict (rowRange A X) LinearMap.id (by
      intro x
      refine ⟨x, ?_⟩
      change (rowMatrix A (freeObject A n).p).toLinearMapRight' x = x
      rw [freeObject_matrix, Matrix.toLinearMapRight'_one]
      rfl)
  have hfb : forward.comp backward = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rfl
  have hbf : backward.comp forward = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  exact isoOfLinearEquiv (LinearEquiv.ofLinearMap forward backward hfb hbf)

private theorem freeIso_hom_apply (n : ℕ)
    (x : (projectiveEquivalence A).functor.obj (freeObject A n)) :
    (freeIso A n).hom.hom.hom x = x.1 := rfl

private theorem freeIso_inv_apply (n : ℕ) (v : Fin n → A) :
    ((freeIso A n).inv.hom.hom v).1 = v := rfl

private def freeMatrixHom {n m : ℕ} (a : Matrix (Fin n) (Fin m) A) :
    freeObject A n ⟶ freeObject A m :=
  (Idempotents.toKaroubi (RankBase A)).map (rowMatrixHom A a)

private theorem freeMatrixHom_matrix {n m : ℕ} (a : Matrix (Fin n) (Fin m) A) :
    rowMatrix A (freeMatrixHom A a).f = a :=
  rowMatrix_rowMatrixHom A a

private theorem freeIso_matrix_square {n m : ℕ} (a : Matrix (Fin n) (Fin m) A) :
    (projectiveEquivalence A).functor.map (freeMatrixHom A a) ≫ (freeIso A m).hom =
      (freeIso A n).hom ≫ FGProjectiveCat.ofHom a.toLinearMapRight' := by
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem freeZeroIsZero : IsZero (freeObject A 0) := by
  apply (IsZero.iff_id_eq_zero (freeObject A 0)).mpr
  apply Idempotents.Karoubi.Hom.ext
  apply rowMatrix_injective A
  ext i j
  exact Fin.elim0 i

private def freeZeroIso : freeObject A 0 ≅ (0 : IdempotentRows A) :=
  (freeZeroIsZero A).isoZero

private def standardRegularIso : standardFree A 1 ≅ regular A :=
  isoOfLinearEquiv
    { toFun := fun v => v 0
      invFun := fun a => fun _ => a
      left_inv := fun v => funext (fun i => congrArg v (Subsingleton.elim (0 : Fin 1) i))
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private def regularIso : (projectiveEquivalence A).functor.obj (freeObject A 1) ≅ regular A :=
  freeIso A 1 ≪≫ standardRegularIso A

private theorem regularIso_hom_apply
    (x : (projectiveEquivalence A).functor.obj (freeObject A 1)) :
    (regularIso A).hom.hom.hom x = x.1 (0 : Fin 1) := rfl

private def leftInclusion (n m : ℕ) : Matrix (Fin n) (Fin (n + m)) A :=
  fun i k => if k = Fin.castAdd m i then 1 else 0

private def leftProjection (n m : ℕ) : Matrix (Fin (n + m)) (Fin n) A :=
  fun k i => if k = Fin.castAdd m i then 1 else 0

private def rightInclusion (n m : ℕ) : Matrix (Fin m) (Fin (n + m)) A :=
  fun j k => if k = Fin.natAdd n j then 1 else 0

private def rightProjection (n m : ℕ) : Matrix (Fin (n + m)) (Fin m) A :=
  fun k j => if k = Fin.natAdd n j then 1 else 0

private theorem left_ne_right (n m : ℕ) (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have hs := congrArg (finSumFinEquiv (m := n) (n := m)).symm h
  have hc : (Sum.inl i : Fin n ⊕ Fin m) = Sum.inr j := by
    simpa only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd] using hs
  cases hc

private theorem leftProjection_apply (n m : ℕ) (v : Fin (n + m) → A) (i : Fin n) :
    (leftProjection A n m).toLinearMapRight' v i = v (Fin.castAdd m i) := by
  change (∑ k : Fin (n + m), v k * (if k = Fin.castAdd m i then 1 else 0)) = _
  rw [Finset.sum_eq_single (Fin.castAdd m i)]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

private theorem rightProjection_apply (n m : ℕ) (v : Fin (n + m) → A) (j : Fin m) :
    (rightProjection A n m).toLinearMapRight' v j = v (Fin.natAdd n j) := by
  change (∑ k : Fin (n + m), v k * (if k = Fin.natAdd n j then 1 else 0)) = _
  rw [Finset.sum_eq_single (Fin.natAdd n j)]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

private theorem leftInclusion_left (n m : ℕ) (v : Fin n → A) (i : Fin n) :
    (leftInclusion A n m).toLinearMapRight' v (Fin.castAdd m i) = v i := by
  change (∑ k : Fin n, v k * (if Fin.castAdd m i = Fin.castAdd m k then 1 else 0)) = _
  simp only [Fin.castAdd_inj]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

private theorem leftInclusion_right (n m : ℕ) (v : Fin n → A) (j : Fin m) :
    (leftInclusion A n m).toLinearMapRight' v (Fin.natAdd n j) = 0 := by
  change (∑ k : Fin n, v k * (if Fin.natAdd n j = Fin.castAdd m k then 1 else 0)) = 0
  apply Finset.sum_eq_zero
  intro k _
  simp [Ne.symm (left_ne_right n m k j)]

private theorem rightInclusion_left (n m : ℕ) (v : Fin m → A) (i : Fin n) :
    (rightInclusion A n m).toLinearMapRight' v (Fin.castAdd m i) = 0 := by
  change (∑ k : Fin m, v k * (if Fin.castAdd m i = Fin.natAdd n k then 1 else 0)) = 0
  apply Finset.sum_eq_zero
  intro k _
  simp [left_ne_right n m i k]

private theorem rightInclusion_right (n m : ℕ) (v : Fin m → A) (j : Fin m) :
    (rightInclusion A n m).toLinearMapRight' v (Fin.natAdd n j) = v j := by
  change (∑ k : Fin m, v k * (if Fin.natAdd n j = Fin.natAdd n k then 1 else 0)) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have hne : Fin.natAdd n j ≠ Fin.natAdd n k := by
      intro h
      have hs := congrArg (finSumFinEquiv (m := n) (n := m)).symm h
      have hjk : j = k := by
        simpa only [finSumFinEquiv_symm_apply_natAdd, Sum.inr.injEq] using hs
      exact hk hjk.symm
    simp [hne]
  · simp

private theorem left_inclusion_projection (n m : ℕ) :
    leftInclusion A n m * leftProjection A n m = 1 := by
  apply Matrix.toLinearMapRight'.injective
  apply LinearMap.ext
  intro v
  funext i
  simp only [Matrix.toLinearMapRight'_mul_apply, leftProjection_apply, leftInclusion_left,
    Matrix.toLinearMapRight'_one, LinearMap.id_apply]

private theorem right_inclusion_projection (n m : ℕ) :
    rightInclusion A n m * rightProjection A n m = 1 := by
  apply Matrix.toLinearMapRight'.injective
  apply LinearMap.ext
  intro v
  funext i
  simp only [Matrix.toLinearMapRight'_mul_apply, rightProjection_apply, rightInclusion_right,
    Matrix.toLinearMapRight'_one, LinearMap.id_apply]

private theorem left_inclusion_right_projection (n m : ℕ) :
    leftInclusion A n m * rightProjection A n m = 0 := by
  apply Matrix.toLinearMapRight'.injective
  apply LinearMap.ext
  intro v
  funext i
  simp only [Matrix.toLinearMapRight'_mul_apply, rightProjection_apply, leftInclusion_right,
    map_zero, LinearMap.zero_apply, Pi.zero_apply]

private theorem right_inclusion_left_projection (n m : ℕ) :
    rightInclusion A n m * leftProjection A n m = 0 := by
  apply Matrix.toLinearMapRight'.injective
  apply LinearMap.ext
  intro v
  funext i
  simp only [Matrix.toLinearMapRight'_mul_apply, leftProjection_apply, rightInclusion_left,
    map_zero, LinearMap.zero_apply, Pi.zero_apply]

private theorem coordinate_reconstruction (n m : ℕ) :
    leftProjection A n m * leftInclusion A n m +
        rightProjection A n m * rightInclusion A n m = 1 := by
  apply Matrix.toLinearMapRight'.injective
  rw [Matrix.toLinearMapRight'.map_add]
  apply LinearMap.ext
  intro v
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [LinearMap.add_apply, Matrix.toLinearMapRight'_mul_apply,
      leftInclusion_left, rightInclusion_left, leftProjection_apply,
      Matrix.toLinearMapRight'_one, LinearMap.id_apply, Pi.add_apply, add_zero]
  · intro j
    simp only [LinearMap.add_apply, Matrix.toLinearMapRight'_mul_apply,
      leftInclusion_right, rightInclusion_right, rightProjection_apply,
      Matrix.toLinearMapRight'_one, LinearMap.id_apply, Pi.add_apply, zero_add]

private theorem freeMatrixHom_one (n : ℕ) :
    freeMatrixHom A (1 : Matrix (Fin n) (Fin n) A) = 𝟙 (freeObject A n) := by
  apply Idempotents.Karoubi.Hom.ext
  apply rowMatrix_injective A
  change rowMatrix A (rowMatrixHom A 1) = rowMatrix A (freeObject A n).p
  rw [rowMatrix_rowMatrixHom, freeObject_matrix]

private theorem freeMatrixHom_zero (n m : ℕ) :
    freeMatrixHom A (0 : Matrix (Fin n) (Fin m) A) = 0 := by
  apply Idempotents.Karoubi.Hom.ext
  apply rowMatrix_injective A
  ext i j
  rfl

private theorem freeMatrixHom_comp {n m k : ℕ}
    (a : Matrix (Fin n) (Fin m) A) (b : Matrix (Fin m) (Fin k) A) :
    freeMatrixHom A a ≫ freeMatrixHom A b = freeMatrixHom A (a * b) := by
  apply Idempotents.Karoubi.Hom.ext
  apply rowMatrix_injective A
  change rowMatrix A (rowMatrixHom A a ≫ rowMatrixHom A b) = rowMatrix A (rowMatrixHom A (a * b))
  rw [rowMatrix_comp, rowMatrix_rowMatrixHom, rowMatrix_rowMatrixHom, rowMatrix_rowMatrixHom]

private theorem freeMatrixHom_add {n m : ℕ} (a b : Matrix (Fin n) (Fin m) A) :
    freeMatrixHom A (a + b) = freeMatrixHom A a + freeMatrixHom A b := by
  apply Idempotents.Karoubi.Hom.ext
  apply rowMatrix_injective A
  change rowMatrix A (rowMatrixHom A (a + b)) = rowMatrix A (rowMatrixHom A a + rowMatrixHom A b)
  rw [rowMatrix_add, rowMatrix_rowMatrixHom, rowMatrix_rowMatrixHom, rowMatrix_rowMatrixHom]

private def freeBiprodIso (n m : ℕ) :
    freeObject A (n + m) ≅ freeObject A n ⊞ freeObject A m where
  hom := biprod.lift (freeMatrixHom A (leftProjection A n m))
    (freeMatrixHom A (rightProjection A n m))
  inv := biprod.desc (freeMatrixHom A (leftInclusion A n m))
    (freeMatrixHom A (rightInclusion A n m))
  hom_inv_id := by
    rw [biprod.lift_desc, freeMatrixHom_comp, freeMatrixHom_comp,
      ← freeMatrixHom_add, coordinate_reconstruction, freeMatrixHom_one]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext'
    all_goals simp only [Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.lift_fst, biprod.lift_snd, Category.id_comp,
      biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd,
      freeMatrixHom_comp, left_inclusion_projection, right_inclusion_projection,
      left_inclusion_right_projection, right_inclusion_left_projection,
      freeMatrixHom_one, freeMatrixHom_zero]

private instance freeBiprodPreserved (n m : ℕ) :
    PreservesBinaryBiproduct (freeObject A n) (freeObject A m)
      (projectiveEquivalence A).functor := by
  let F := (projectiveEquivalence A).functor
  let : PreservesBiproduct (pairFunction (freeObject A n) (freeObject A m)) F := inferInstance
  exact preservesBinaryBiproduct_of_preservesBiproduct F (freeObject A n) (freeObject A m)

private theorem standardAdd_fst (n m : ℕ) (v : Fin (n + m) → A) (i : Fin n) :
    (biprod.fst : standardFree A n ⊞ standardFree A m ⟶ standardFree A n).hom.hom
        ((standardFreeAddIso A n m).hom v) i = v (Fin.castAdd m i) := by
  let T := standardFreeAddIso A n m
  let x := T.hom v
  have h := standardFreeAddIso_inv_apply_fun A n m x
  have hv : T.inv.hom.hom x = v :=
    congrArg (fun f : standardFree A (n + m) ⟶ standardFree A (n + m) => f.hom.hom v)
      T.hom_inv_id
  have hi := congrFun (hv.symm.trans h) (Fin.castAdd m i)
  simpa only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl,
    biprodCarrierLinearEquiv_apply_fst] using hi.symm

private theorem standardAdd_snd (n m : ℕ) (v : Fin (n + m) → A) (j : Fin m) :
    (biprod.snd : standardFree A n ⊞ standardFree A m ⟶ standardFree A m).hom.hom
        ((standardFreeAddIso A n m).hom v) j = v (Fin.natAdd n j) := by
  let T := standardFreeAddIso A n m
  let x := T.hom v
  have h := standardFreeAddIso_inv_apply_fun A n m x
  have hv : T.inv.hom.hom x = v :=
    congrArg (fun f : standardFree A (n + m) ⟶ standardFree A (n + m) => f.hom.hom v)
      T.hom_inv_id
  have hj := congrFun (hv.symm.trans h) (Fin.natAdd n j)
  simpa only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr,
    biprodCarrierLinearEquiv_apply_snd] using hj.symm

private theorem freeBiprod_image (n m : ℕ) :
    (projectiveEquivalence A).functor.mapIso (freeBiprodIso A n m) ≪≫
        (projectiveEquivalence A).functor.mapBiprod (freeObject A n) (freeObject A m) ≪≫
          biprod.mapIso (freeIso A n) (freeIso A m) =
      freeIso A (n + m) ≪≫ standardFreeAddIso A n m := by
  let F := (projectiveEquivalence A).functor
  let B := freeBiprodIso A n m
  let C := F.mapBiprod (freeObject A n) (freeObject A m)
  have hf : C.hom ≫ biprod.fst = F.map biprod.fst := by
    simp only [C, Functor.mapBiprod_hom, biprod.lift_fst]
  have hs : C.hom ≫ biprod.snd = F.map biprod.snd := by
    simp only [C, Functor.mapBiprod_hom, biprod.lift_snd]
  apply Iso.ext
  apply biprod.hom_ext
  · change (F.map B.hom ≫ C.hom ≫
        biprod.map (freeIso A n).hom (freeIso A m).hom) ≫ biprod.fst = _
    calc
      _ = F.map B.hom ≫ (C.hom ≫ biprod.fst) ≫ (freeIso A n).hom := by
        rw [Category.assoc, Category.assoc, biprod.map_fst]
        simp only [Category.assoc]
      _ = F.map B.hom ≫ F.map biprod.fst ≫ (freeIso A n).hom := by rw [hf]
      _ = F.map (B.hom ≫ biprod.fst) ≫ (freeIso A n).hom := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
      _ = F.map (freeMatrixHom A (leftProjection A n m)) ≫ (freeIso A n).hom := by
        rw [show B.hom ≫ biprod.fst = freeMatrixHom A (leftProjection A n m) from
          biprod.lift_fst _ _]
      _ = (freeIso A (n + m)).hom ≫ FGProjectiveCat.ofHom
          (leftProjection A n m).toLinearMapRight' := freeIso_matrix_square A _
      _ = _ := by
        apply FGProjectiveCat.hom_ext
        apply LinearMap.ext
        intro x
        funext i
        change (leftProjection A n m).toLinearMapRight' x.1 i =
          (biprod.fst : standardFree A n ⊞ standardFree A m ⟶ standardFree A n).hom.hom
            ((standardFreeAddIso A n m).hom x.1) i
        rw [leftProjection_apply, standardAdd_fst]
  · change (F.map B.hom ≫ C.hom ≫
        biprod.map (freeIso A n).hom (freeIso A m).hom) ≫ biprod.snd = _
    calc
      _ = F.map B.hom ≫ (C.hom ≫ biprod.snd) ≫ (freeIso A m).hom := by
        rw [Category.assoc, Category.assoc, biprod.map_snd]
        simp only [Category.assoc]
      _ = F.map B.hom ≫ F.map biprod.snd ≫ (freeIso A m).hom := by rw [hs]
      _ = F.map (B.hom ≫ biprod.snd) ≫ (freeIso A m).hom := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
      _ = F.map (freeMatrixHom A (rightProjection A n m)) ≫ (freeIso A m).hom := by
        rw [show B.hom ≫ biprod.snd = freeMatrixHom A (rightProjection A n m) from
          biprod.lift_snd _ _]
      _ = (freeIso A (n + m)).hom ≫ FGProjectiveCat.ofHom
          (rightProjection A n m).toLinearMapRight' := freeIso_matrix_square A _
      _ = _ := by
        apply FGProjectiveCat.hom_ext
        apply LinearMap.ext
        intro x
        funext j
        change (rightProjection A n m).toLinearMapRight' x.1 j =
          (biprod.snd : standardFree A n ⊞ standardFree A m ⟶ standardFree A m).hom.hom
            ((standardFreeAddIso A n m).hom x.1) j
        rw [rightProjection_apply, standardAdd_snd]

private def freeAut (n : ℕ) (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    freeObject A n ≅ freeObject A n where
  hom := freeMatrixHom A (↑(MulOpposite.unop g) : Matrix (Fin n) (Fin n) A)
  inv := freeMatrixHom A (↑((MulOpposite.unop g)⁻¹) : Matrix (Fin n) (Fin n) A)
  hom_inv_id := by
    rw [freeMatrixHom_comp, Units.mul_inv, freeMatrixHom_one]
  inv_hom_id := by
    rw [freeMatrixHom_comp, Units.inv_mul, freeMatrixHom_one]

private theorem freeAut_characteristic (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    (freeIso A n).conjAut
        (Aut.of ((projectiveEquivalence A).functor.mapIso (freeAut A n g))) =
      finiteOppositeGLAutRowMulEquiv A n g := by
  have hc := Iso.conjAut_apply (freeIso A n)
    (Aut.of ((projectiveEquivalence A).functor.mapIso (freeAut A n g)))
  apply Aut.ext
  apply hc.trans
  apply Iso.ext
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro v
  change (↑(MulOpposite.unop g) : Matrix (Fin n) (Fin n) A).toLinearMapRight' v =
    (finiteOppositeGLAutRowMulEquiv A n g).asIso.hom v
  exact (finiteOppositeGLAutRowMulEquiv_apply A n g v).symm

private theorem freeAut_hom_square (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    (projectiveEquivalence A).functor.map (freeAut A n g).hom ≫ (freeIso A n).hom =
      (freeIso A n).hom ≫ (finiteOppositeGLAutRowMulEquiv A n g).asIso.hom := by
  let H := freeIso A n
  let G := (projectiveEquivalence A).functor.mapIso (freeAut A n g)
  have h : H.symm ≪≫ G ≪≫ H = (finiteOppositeGLAutRowMulEquiv A n g).asIso :=
    (Iso.conjAut_apply H (Aut.of G)).symm.trans
      (congrArg Aut.asIso (freeAut_characteristic A n g))
  have hh := H.hom ≫= congrArg Iso.hom h
  simpa only [H, G, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc] using hh

private theorem freeBiprod_mapAut_square (n m : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ)
    (h : (Matrix.GeneralLinearGroup (Fin m) A)ᵐᵒᵖ) :
    (projectiveEquivalence A).functor.mapIso
        (biprod.mapIso (freeAut A n g) (freeAut A m h)) ≪≫
      (projectiveEquivalence A).functor.mapBiprod (freeObject A n) (freeObject A m) =
    (projectiveEquivalence A).functor.mapBiprod (freeObject A n) (freeObject A m) ≪≫
      biprod.mapIso ((projectiveEquivalence A).functor.mapIso (freeAut A n g))
        ((projectiveEquivalence A).functor.mapIso (freeAut A m h)) := by
  apply Iso.ext
  apply biprod.hom_ext
  · simp only [Iso.trans_hom, Functor.mapIso_hom, biprod.mapIso_hom, Functor.mapBiprod_hom,
      Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst,
      ← Functor.map_comp]
  · simp only [Iso.trans_hom, Functor.mapIso_hom, biprod.mapIso_hom, Functor.mapBiprod_hom,
      Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc, biprod.map_snd,
      ← Functor.map_comp]

private theorem freeBiprod_isoAut_square (n m : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ)
    (h : (Matrix.GeneralLinearGroup (Fin m) A)ᵐᵒᵖ) :
    biprod.mapIso ((projectiveEquivalence A).functor.mapIso (freeAut A n g))
        ((projectiveEquivalence A).functor.mapIso (freeAut A m h)) ≪≫
      biprod.mapIso (freeIso A n) (freeIso A m) =
    biprod.mapIso (freeIso A n) (freeIso A m) ≪≫
      biprod.mapIso (finiteOppositeGLAutRowMulEquiv A n g).asIso
        (finiteOppositeGLAutRowMulEquiv A m h).asIso := by
  apply Iso.ext
  apply biprod.hom_ext
  · change biprod.map ((projectiveEquivalence A).functor.map (freeAut A n g).hom)
        ((projectiveEquivalence A).functor.map (freeAut A m h).hom) ≫
        biprod.map (freeIso A n).hom (freeIso A m).hom ≫ biprod.fst =
      biprod.map (freeIso A n).hom (freeIso A m).hom ≫
        biprod.map (finiteOppositeGLAutRowMulEquiv A n g).asIso.hom
          (finiteOppositeGLAutRowMulEquiv A m h).asIso.hom ≫ biprod.fst
    simp only [biprod.map_fst, biprod.map_fst_assoc, freeAut_hom_square]
  · change biprod.map ((projectiveEquivalence A).functor.map (freeAut A n g).hom)
        ((projectiveEquivalence A).functor.map (freeAut A m h).hom) ≫
        biprod.map (freeIso A n).hom (freeIso A m).hom ≫ biprod.snd =
      biprod.map (freeIso A n).hom (freeIso A m).hom ≫
        biprod.map (finiteOppositeGLAutRowMulEquiv A n g).asIso.hom
          (finiteOppositeGLAutRowMulEquiv A m h).asIso.hom ≫ biprod.snd
    simp only [biprod.map_snd, biprod.map_snd_assoc, freeAut_hom_square]

private theorem freeBiprod_inverse_comparison (n m : ℕ) :
    ((projectiveEquivalence A).functor.mapIso (freeBiprodIso A n m)).symm ≪≫
        freeIso A (n + m) =
      (projectiveEquivalence A).functor.mapBiprod (freeObject A n) (freeObject A m) ≪≫
        biprod.mapIso (freeIso A n) (freeIso A m) ≪≫ (standardFreeAddIso A n m).symm := by
  let B := (projectiveEquivalence A).functor.mapIso (freeBiprodIso A n m)
  let T := standardFreeAddIso A n m
  have h := congrArg (fun e => B.symm ≪≫ e ≪≫ T.symm) (freeBiprod_image A n m)
  simpa only [B, T, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
    Iso.trans_refl] using h.symm

private theorem freeBiprod_mapAut_conj (n m : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ)
    (h : (Matrix.GeneralLinearGroup (Fin m) A)ᵐᵒᵖ) :
    ((projectiveEquivalence A).functor.mapBiprod (freeObject A n) (freeObject A m)).conjAut
        (Aut.of ((projectiveEquivalence A).functor.mapIso
          (biprod.mapIso (freeAut A n g) (freeAut A m h)))) =
      Aut.of (biprod.mapIso ((projectiveEquivalence A).functor.mapIso (freeAut A n g))
        ((projectiveEquivalence A).functor.mapIso (freeAut A m h))) := by
  let C := (projectiveEquivalence A).functor.mapBiprod (freeObject A n) (freeObject A m)
  let G := (projectiveEquivalence A).functor.mapIso
    (biprod.mapIso (freeAut A n g) (freeAut A m h))
  have hc := C.inv ≫= congrArg Iso.hom (freeBiprod_mapAut_square A n m g h)
  apply Aut.ext
  apply (Iso.conjAut_apply C (Aut.of G)).trans
  apply Iso.ext
  calc
    _ = C.inv ≫ G.hom ≫ C.hom := rfl
    _ = _ := by
      simpa only [C, G, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc] using hc

private theorem freeBiprod_isoAut_conj (n m : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ)
    (h : (Matrix.GeneralLinearGroup (Fin m) A)ᵐᵒᵖ) :
    (biprod.mapIso (freeIso A n) (freeIso A m)).conjAut
        (Aut.of (biprod.mapIso
          ((projectiveEquivalence A).functor.mapIso (freeAut A n g))
          ((projectiveEquivalence A).functor.mapIso (freeAut A m h)))) =
      Aut.of (biprod.mapIso (finiteOppositeGLAutRowMulEquiv A n g).asIso
        (finiteOppositeGLAutRowMulEquiv A m h).asIso) := by
  let C := biprod.mapIso (freeIso A n) (freeIso A m)
  let G := biprod.mapIso ((projectiveEquivalence A).functor.mapIso (freeAut A n g))
    ((projectiveEquivalence A).functor.mapIso (freeAut A m h))
  have hc := C.inv ≫= congrArg Iso.hom (freeBiprod_isoAut_square A n m g h)
  apply Aut.ext
  apply (Iso.conjAut_apply C (Aut.of G)).trans
  apply Iso.ext
  calc
    _ = C.inv ≫ G.hom ≫ C.hom := rfl
    _ = _ := by
      simpa only [C, G, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc] using hc

private theorem freeAut_comparison_injective (n : ℕ) :
    Function.Injective (fun g : freeObject A n ≅ freeObject A n =>
      (freeIso A n).conjAut (Aut.of ((projectiveEquivalence A).functor.mapIso g))) := by
  intro g h he
  apply Iso.ext
  apply (projectiveEquivalence A).functor.map_injective
  exact congrArg (fun a => a.asIso.hom) ((freeIso A n).conjAut.injective he)

private theorem freeAut_blockDiagonal (n m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) A)
    (h : Matrix.GeneralLinearGroup (Fin m) A) :
    freeAut A (n + m)
        (MulOpposite.op (Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := m))
          (Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal g h))) =
      ((freeBiprodIso A n m).symm.conjAut
        (Aut.of (biprod.mapIso (freeAut A n (MulOpposite.op g))
          (freeAut A m (MulOpposite.op h))))).asIso := by
  apply freeAut_comparison_injective A (n + m)
  dsimp only
  let F := (projectiveEquivalence A).functor
  let B := freeBiprodIso A n m
  let H := freeIso A (n + m)
  let C := F.mapBiprod (freeObject A n) (freeObject A m)
  let J := biprod.mapIso (freeIso A n) (freeIso A m)
  let T := standardFreeAddIso A n m
  let a : Aut (freeObject A n ⊞ freeObject A m) :=
    Aut.of (biprod.mapIso (freeAut A n (MulOpposite.op g))
      (freeAut A m (MulOpposite.op h)))
  let fa : Aut (F.obj (freeObject A n ⊞ freeObject A m)) :=
    F.mapAut (freeObject A n ⊞ freeObject A m) a
  have hmap : F.mapIso (B.symm.conjAut a).asIso =
      ((F.mapIso B).symm.conjAut fa).asIso :=
    (Functor.map_conjAut F B.symm a).trans
      (congrArg (fun e => (e.conjAut fa).asIso) (Functor.mapIso_symm F B))
  have hr : H.conjAut (Aut.of (F.mapIso (B.symm.conjAut a).asIso)) =
      T.symm.conjAut
        (Aut.of (biprod.mapIso
          (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso
          (finiteOppositeGLAutRowMulEquiv A m (MulOpposite.op h)).asIso)) := by
    calc
      _ = H.conjAut (Aut.of ((F.mapIso B).symm.conjAut fa).asIso) :=
        congrArg (fun e => H.conjAut (Aut.of e)) hmap
      _ = ((F.mapIso B).symm ≪≫ H).conjAut fa :=
        (Iso.trans_conjAut _ _ _).symm
      _ = (C ≪≫ J ≪≫ T.symm).conjAut fa :=
        congrArg (fun e => e.conjAut fa) (freeBiprod_inverse_comparison A n m)
      _ = T.symm.conjAut (J.conjAut (C.conjAut fa)) := by
        simp only [Iso.trans_conjAut]
      _ = _ := by
        exact congrArg (fun e => T.symm.conjAut (J.conjAut e))
          (freeBiprod_mapAut_conj A n m (MulOpposite.op g) (MulOpposite.op h)) |>.trans
            (congrArg T.symm.conjAut
              (freeBiprod_isoAut_conj A n m (MulOpposite.op g) (MulOpposite.op h)))
  exact (freeAut_characteristic A (n + m) _).trans
    ((finiteOppositeGLAutRowMulEquiv_blockDiagonal A n m g h).trans hr.symm)

private theorem freeAut_one (n : ℕ) :
    freeAut A n (MulOpposite.op (1 : Matrix.GeneralLinearGroup (Fin n) A)) =
      Iso.refl (freeObject A n) := by
  apply Iso.ext
  exact freeMatrixHom_one A n

private theorem freeAut_blockStabilization (n m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    freeAut A (n + m) (MulOpposite.op (Matrix.GeneralLinearGroup.blockStabilization n m A g)) =
      ((freeBiprodIso A n m).symm.conjAut
        (Aut.of (biprod.mapIso
          (freeAut A n (MulOpposite.op g)) (Iso.refl (freeObject A m))))).asIso := by
  have hb : Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal
      g (1 : Matrix.GeneralLinearGroup (Fin m) A) =
        Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin m) A g := by
    rw [Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal_eq_blockDiagonalHom]
    exact Matrix.GeneralLinearGroup.blockDiagonalHom_one_right (m := Fin m) g
  simpa only [hb, Matrix.GeneralLinearGroup.blockStabilization,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, freeAut_one] using
    freeAut_blockDiagonal A n m g 1

private theorem freeAut_stabilization (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) A) :
    freeAut A (n + 1) (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization A g)) =
      ((freeBiprodIso A n 1).symm.conjAut
        (Aut.of (biprod.mapIso
          (freeAut A n (MulOpposite.op g)) (Iso.refl (freeObject A 1))))).asIso :=
  freeAut_blockStabilization A n 1 g

private def regularSuccessorIso (n : ℕ) :
    (projectiveEquivalence A).functor.obj (freeObject A (n + 1)) ≅
      standardFree A n ⊞ regular A :=
  (projectiveEquivalence A).functor.mapIso (freeBiprodIso A n 1) ≪≫
    (projectiveEquivalence A).functor.mapBiprod (freeObject A n) (freeObject A 1) ≪≫
      biprod.mapIso (freeIso A n) (regularIso A)

private theorem regularSuccessor_image (n : ℕ) :
    regularSuccessorIso A n = freeIso A (n + 1) ≪≫ standardFreeAddIso A n 1 ≪≫
      biprod.mapIso (Iso.refl (standardFree A n)) (standardRegularIso A) := by
  let R := biprod.mapIso (Iso.refl (standardFree A n)) (standardRegularIso A)
  have hh : biprod.mapIso (freeIso A n) (freeIso A 1) ≪≫ R =
      biprod.mapIso (freeIso A n) (regularIso A) := by
    apply Iso.ext
    apply biprod.hom_ext
    · simp only [R, Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.map_fst, Iso.refl_hom,
        Category.comp_id]
    · simp only [R, Iso.trans_hom, biprod.mapIso_hom, Category.assoc,
        biprod.map_snd, biprod.map_snd_assoc, regularIso]
  have he := congrArg (fun e => e ≪≫ R) (freeBiprod_image A n 1)
  simpa only [regularSuccessorIso, R, Iso.trans_assoc, hh] using he

private theorem regularSuccessor_stabilization (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    (regularSuccessorIso A n).conjAut
        (Aut.of ((projectiveEquivalence A).functor.mapIso
          (freeAut A (n + 1) (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization A g))))) =
      Aut.of (biprod.mapIso
        (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso
        (Iso.refl (regular A))) := by
  let T := standardFreeAddIso A n 1
  let R := biprod.mapIso (Iso.refl (standardFree A n)) (standardRegularIso A)
  let b : Aut (standardFree A n ⊞ standardFree A 1) :=
    Aut.of (biprod.mapIso
      (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso
      (Iso.refl (standardFree A 1)))
  have ht : T.conjAut (T.symm.conjAut b) = b := by
    apply Aut.ext
    rw [Iso.conjAut_apply, Iso.conjAut_apply]
    simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  have hr : R.conjAut b =
      Aut.of (biprod.mapIso
        (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso
        (Iso.refl (regular A))) := by
    have hn : b.asIso ≪≫ R = R ≪≫
        biprod.mapIso (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso
          (Iso.refl (regular A)) := by
      apply Iso.ext
      apply biprod.hom_ext
      · change biprod.map (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso.hom
            (𝟙 (standardFree A 1)) ≫
            biprod.map (𝟙 (standardFree A n)) (standardRegularIso A).hom ≫ biprod.fst =
          biprod.map (𝟙 (standardFree A n)) (standardRegularIso A).hom ≫
            biprod.map (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso.hom
              (𝟙 (regular A)) ≫ biprod.fst
        simp only [biprod.map_fst, biprod.map_fst_assoc, Category.id_comp, Category.comp_id]
      · change biprod.map (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso.hom
            (𝟙 (standardFree A 1)) ≫
            biprod.map (𝟙 (standardFree A n)) (standardRegularIso A).hom ≫ biprod.snd =
          biprod.map (𝟙 (standardFree A n)) (standardRegularIso A).hom ≫
            biprod.map (finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso.hom
              (𝟙 (regular A)) ≫ biprod.snd
        simp only [biprod.map_snd, biprod.map_snd_assoc, Category.id_comp, Category.comp_id]
    apply Aut.ext
    rw [Iso.conjAut_apply]
    have hi := congrArg (fun e => R.symm ≪≫ e) hn
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using hi
  let a : Aut ((projectiveEquivalence A).functor.obj (freeObject A (n + 1))) :=
    Aut.of ((projectiveEquivalence A).functor.mapIso
      (freeAut A (n + 1) (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization A g))))
  let Q : FGProjectiveCat.{u} A := standardFree A n ⊞ regular A
  let x0 : Aut Q := (regularSuccessorIso A n).conjAut a
  let x1 : Aut Q := (freeIso A (n + 1) ≪≫ T ≪≫ R).conjAut a
  let x2 : Aut Q := R.conjAut (T.conjAut ((freeIso A (n + 1)).conjAut a))
  let x3 : Aut Q := R.conjAut (T.conjAut
    (finiteOppositeGLAutRowMulEquiv A (n + 1)
      (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization A g))))
  let x4 : Aut Q := R.conjAut (T.conjAut (T.symm.conjAut b))
  let x5 : Aut Q := R.conjAut b
  have h1 : x0 = x1 := congrArg (fun e => e.conjAut a) (regularSuccessor_image A n)
  have h2 : x1 = x2 := by
    simp only [x1, x2, Iso.trans_conjAut]
  have h3 : x2 = x3 := congrArg (fun e => R.conjAut (T.conjAut e))
    (freeAut_characteristic A (n + 1) _)
  have h4 : x3 = x4 := congrArg (fun e => R.conjAut (T.conjAut e))
    (finiteOppositeGLAutRowMulEquiv_stabilization A n g)
  have h5 : x4 = x5 := congrArg (fun e => R.conjAut e) ht
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans hr))))

end FGProjectiveCat

namespace FGProjectiveCat

open scoped ZeroObject

variable (A : Type u) [Ring A]

/-- The standard matrix category restricted to the literal natural-rank tuples. -/
public abbrev FiniteRowRanks :=
  InducedCategory (Mat_ (SingleObj Aᵐᵒᵖ))
    (fun n : ℕ =>
      ({ ι := Fin n, X := fun _ => Quiver.SingleObj.star Aᵐᵒᵖ } :
        Mat_ (SingleObj Aᵐᵒᵖ)))

/-- The standard Karoubi completion of the natural-rank row category. -/
public abbrev IdempotentModel := Idempotents.Karoubi (FiniteRowRanks A)

namespace FiniteRowRanks

public instance instHasFiniteBiproducts : HasFiniteBiproducts (FiniteRowRanks A) :=
  FGProjectiveCat.rankBaseHasFiniteBiproducts A

end FiniteRowRanks

namespace IdempotentModel

public instance instHasBinaryBiproducts : HasBinaryBiproducts (IdempotentModel A) :=
  hasBinaryBiproducts_of_finite_biproducts (IdempotentModel A)

public instance instExactCategory : ExactCategory (IdempotentModel A) :=
  ExactCategory.splitExactCategory

/-- Additive row coordinates, with the original opposite single-object convention. -/
public def rowHomEquiv (n m : ℕ) :
    let sourceRank : FiniteRowRanks A := n
    let targetRank : FiniteRowRanks A := m
    (sourceRank ⟶ targetRank) ≃+ Matrix (Fin n) (Fin m) A where
  toFun := FGProjectiveCat.rowMatrix A
  invFun := FGProjectiveCat.rowMatrixHom A
  left_inv := FGProjectiveCat.rowMatrixHom_rowMatrix A
  right_inv := FGProjectiveCat.rowMatrix_rowMatrixHom A
  map_add' := FGProjectiveCat.rowMatrix_add A

/-- The actual range submodule of an idempotent's row operator. -/
public abbrev range (P : IdempotentModel A) : Submodule A (Fin P.X → A) :=
  LinearMap.range (rowHomEquiv A P.X P.X P.p).toLinearMapRight'

public instance instRangeFinite (P : IdempotentModel A) : Module.Finite A (range A P) :=
  FGProjectiveCat.rowRangeFiniteInstance A P

public instance instRangeProjective (P : IdempotentModel A) :
    Module.Projective A (range A P) :=
  FGProjectiveCat.rowRangeProjectiveInstance A P

/-- The actual row-range equivalence onto all finitely generated projectives. -/
public def equivalence : IdempotentModel A ≌ FGProjectiveCat.{u} A :=
  FGProjectiveCat.projectiveEquivalence A

public instance instEquivalenceFunctorAdditive : (equivalence A).functor.Additive :=
  FGProjectiveCat.projectiveEquivalenceFunctorAdditive A

public instance instEquivalenceInverseAdditive : (equivalence A).inverse.Additive :=
  FGProjectiveCat.projectiveEquivalenceInverseAdditive A

public instance instEquivalenceFunctorIsExact : (equivalence A).functor.IsExact :=
  FGProjectiveCat.projectiveEquivalenceFunctorExact A

public instance instEquivalenceInverseIsExact : (equivalence A).inverse.IsExact :=
  FGProjectiveCat.projectiveEquivalenceInverseExact A

/-- Equality with the actual range object, for ordinary public carrier transport. -/
public theorem equivalence_obj (P : IdempotentModel A) :
    (equivalence A).functor.obj P = FGProjectiveCat.of (R := A) (range A P) := by
  apply ObjectProperty.FullSubcategory.ext
  rfl

/-- The specified free comparison is the identity-range inclusion and lift. -/
public def freeIso (n : ℕ) :
    (equivalence A).functor.obj ((Idempotents.toKaroubi (FiniteRowRanks A)).obj n) ≅
      FGProjectiveCat.standardFree A n :=
  FGProjectiveCat.freeIso A n

/-- The specified rank-zero comparison is the existing IsZero.isoZero isomorphism. -/
public def freeZeroIso :
    (Idempotents.toKaroubi (FiniteRowRanks A)).obj (0 : ℕ) ≅
      (0 : IdempotentModel A) :=
  FGProjectiveCat.freeZeroIso A

/-- The fixed rank-zero comparison is independent of the proof that the object is zero. -/
public theorem freeZeroIso_characteristic
    (h : IsZero ((Idempotents.toKaroubi (FiniteRowRanks A)).obj (0 : ℕ))) :
    freeZeroIso A = h.isoZero := by
  change (FGProjectiveCat.freeZeroIsZero A).isoZero = h.isoZero
  exact congrArg (fun h0 : IsZero ((Idempotents.toKaroubi (FiniteRowRanks A)).obj (0 : ℕ)) =>
    h0.isoZero) (Subsingleton.elim _ _)


/-- The specified regular comparison evaluates the unique rank-one coordinate. -/
public def regularIso :
    (equivalence A).functor.obj ((Idempotents.toKaroubi (FiniteRowRanks A)).obj (1 : ℕ)) ≅
      FGProjectiveCat.regular A :=
  FGProjectiveCat.regularIso A

/-- The literal coordinate comparison with the standard Karoubi biproduct. -/
public def freeBiprodIso (n m : ℕ) :
    (Idempotents.toKaroubi (FiniteRowRanks A)).obj (n + m) ≅
      (Idempotents.toKaroubi (FiniteRowRanks A)).obj n ⊞
        (Idempotents.toKaroubi (FiniteRowRanks A)).obj m :=
  FGProjectiveCat.freeBiprodIso A n m

/-- The original opposite general-linear row matrix and its inverse. -/
public def freeAut (n : ℕ) (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    (Idempotents.toKaroubi (FiniteRowRanks A)).obj n ≅
      (Idempotents.toKaroubi (FiniteRowRanks A)).obj n :=
  FGProjectiveCat.freeAut A n g

public instance instFreeBiprodPreserved (n m : ℕ) :
    PreservesBinaryBiproduct ((Idempotents.toKaroubi (FiniteRowRanks A)).obj n)
      ((Idempotents.toKaroubi (FiniteRowRanks A)).obj m) (equivalence A).functor :=
  FGProjectiveCat.freeBiprodPreserved A n m

/-- The image of the rank-one biproduct comparison with its regular factor. -/
public def regularSuccessorIso (n : ℕ) :
    (equivalence A).functor.obj
        ((Idempotents.toKaroubi (FiniteRowRanks A)).obj (n + 1)) ≅
      FGProjectiveCat.standardFree A n ⊞ FGProjectiveCat.regular A :=
  FGProjectiveCat.regularSuccessorIso A n

/-- Complete coordinates, corners, actual range maps and split-exact realization. -/
public theorem equivalence_characteristic :
    let E := equivalence A
    let H := fun n m => rowHomEquiv A n m
    let e := fun P : IdempotentModel A => H P.X P.X P.p
    let a := fun {P Q : IdempotentModel A} (f : P ⟶ Q) => H P.X Q.X f.f
    let r := fun P : IdempotentModel A => eqToIso (equivalence_obj A P)
    (∀ (n m : FiniteRowRanks A) (f : n ⟶ m)
      (i : Fin n) (j : Fin m), H n m f i j = MulOpposite.unop (f.hom i j)) ∧
    (∀ n : FiniteRowRanks A, H n n (𝟙 n) = 1) ∧
    (∀ (n m k : FiniteRowRanks A) (f : n ⟶ m) (g : m ⟶ k),
      H n k (f ≫ g) = H n m f * H m k g) ∧
    (∀ P : IdempotentModel A, e P * e P = e P) ∧
    (∀ P : IdempotentModel A, a (𝟙 P) = e P) ∧
    (∀ (P Q S : IdempotentModel A) (f : P ⟶ Q) (g : Q ⟶ S),
      a (f ≫ g) = a f * a g) ∧
    (∀ (P Q : IdempotentModel A) (f g : P ⟶ Q), a (f + g) = a f + a g) ∧
    (∀ (P Q : IdempotentModel A) (f : P ⟶ Q),
      e P * a f = a f ∧ a f * e Q = a f) ∧
    (∀ (P Q : IdempotentModel A) (f g : P ⟶ Q), a f = a g ↔ f = g) ∧
    (∀ (P Q : IdempotentModel A) (b : Matrix (Fin P.X) (Fin Q.X) A),
      e P * b * e Q = b → ∃! f : P ⟶ Q, a f = b) ∧
    (∀ (P Q : IdempotentModel A) (f : P ⟶ Q) (x : range A P),
      (((r P).inv ≫ E.functor.map f ≫ (r Q).hom).hom.hom x).val =
        (a f).toLinearMapRight' x.val) ∧
    (∀ (P Q : IdempotentModel A) (L : range A P →ₗ[A] range A Q),
      ∃! f : P ⟶ Q,
        a f = ((range A Q).subtype.comp
          (L.comp (e P).toLinearMapRight'.rangeRestrict)).toMatrixRight' ∧
        ((r P).inv ≫ E.functor.map f ≫ (r Q).hom).hom.hom = L) ∧
    (∀ P : FGProjectiveCat.{u} A,
      ∃ Q : IdempotentModel A, Nonempty (E.functor.obj Q ≅ P)) ∧
    E.functor.Additive ∧ E.inverse.Additive ∧ E.functor.IsExact ∧ E.inverse.IsExact := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    inferInstance, inferInstance, inferInstance, inferInstance⟩
  · intro n m f i j
    rfl
  · exact FGProjectiveCat.rowMatrix_id A
  · intro n m k f g
    exact FGProjectiveCat.rowMatrix_comp A f g
  · exact FGProjectiveCat.rowMatrix_idempotent A
  · intro P
    rfl
  · intro P Q S f g
    exact FGProjectiveCat.rowMatrix_comp A f.f g.f
  · intro P Q f g
    exact FGProjectiveCat.rowMatrix_add A f.f g.f
  · intro P Q f
    exact ⟨FGProjectiveCat.rowCorner_left A f, FGProjectiveCat.rowCorner_right A f⟩
  · intro P Q f g
    constructor
    · intro h
      apply Idempotents.Karoubi.Hom.ext
      exact FGProjectiveCat.rowMatrix_injective A h
    · rintro rfl
      rfl
  · intro P Q b hb
    let f : P ⟶ Q :=
      { f := FGProjectiveCat.rowMatrixHom A b
        comm := by
          apply FGProjectiveCat.rowMatrix_injective A
          rw [FGProjectiveCat.rowMatrix_comp, FGProjectiveCat.rowMatrix_comp,
            FGProjectiveCat.rowMatrix_rowMatrixHom]
          exact (Matrix.mul_assoc _ _ _).symm.trans hb }
    have hf : rowHomEquiv A P.X Q.X f.f = b :=
      FGProjectiveCat.rowMatrix_rowMatrixHom A b
    refine ⟨f, hf, ?_⟩
    intro g hg
    apply Idempotents.Karoubi.Hom.ext
    exact FGProjectiveCat.rowMatrix_injective A (hg.trans hf.symm)
  · intro P Q f x
    rfl
  · intro P Q L
    let f := FGProjectiveCat.rowCornerPreimage A L
    have hm : ((eqToIso (equivalence_obj A P)).inv ≫ (equivalence A).functor.map f ≫
        (eqToIso (equivalence_obj A Q)).hom).hom.hom = L := by
      change FGProjectiveCat.rowCornerLinear A f = L
      exact congrArg (fun z : FGProjectiveCat.rowObject A P ⟶
        FGProjectiveCat.rowObject A Q => z.hom.hom)
          ((FGProjectiveCat.realizationFullyFaithful A).map_preimage
            (FGProjectiveCat.ofHom L))
    have hb : rowHomEquiv A P.X Q.X f.f =
        ((range A Q).subtype.comp
          (L.comp (rowHomEquiv A P.X P.X P.p).toLinearMapRight'.rangeRestrict)).toMatrixRight' :=
      FGProjectiveCat.rowMatrix_rowMatrixHom A _
    refine ⟨f, ⟨hb, hm⟩, ?_⟩
    intro g hg
    apply (equivalence A).functor.map_injective
    apply FGProjectiveCat.hom_ext
    change FGProjectiveCat.rowCornerLinear A g = FGProjectiveCat.rowCornerLinear A f
    exact hg.2.trans hm.symm
  · exact FGProjectiveCat.realizationEssSurj A

/-- The complete actual free, zero, arbitrary-matrix and regular carrier laws. -/
public theorem free_characteristic :
    let C := FiniteRowRanks A
    let E := equivalence A
    let F := fun n : ℕ => (Idempotents.toKaroubi C).obj n
    let H := fun n => freeIso A n
    let r := fun P : IdempotentModel A => eqToIso (equivalence_obj A P)
    (∀ n : ℕ, rowHomEquiv A n n (F n).p = 1) ∧
    (∀ (n : ℕ) (x : range A (F n)), ((r (F n)).inv ≫ (H n).hom).hom.hom x = x.val) ∧
    (∀ (n : ℕ) (v : Fin n → A), (((H n).inv ≫ (r (F n)).hom).hom.hom v).val = v) ∧
    (∀ (n m : ℕ) (b : Matrix (Fin n) (Fin m) A),
      E.functor.map ((Idempotents.toKaroubi C).map ((rowHomEquiv A n m).symm b)) ≫
          (H m).hom = (H n).hom ≫ FGProjectiveCat.ofHom b.toLinearMapRight') ∧
    IsZero (F 0) ∧
    (∀ x : range A (F 1),
      ((r (F 1)).inv ≫ (regularIso A).hom).hom.hom x = x.val (0 : Fin 1)) ∧
    (∀ z : A, (((regularIso A).inv ≫ (r (F 1)).hom).hom.hom z).val =
      fun _ : Fin 1 => z) := by
  dsimp only
  refine ⟨FGProjectiveCat.freeObject_matrix A, ?_, ?_, ?_,
    FGProjectiveCat.freeZeroIsZero A, ?_, ?_⟩
  · intro n x
    exact FGProjectiveCat.freeIso_hom_apply A n x
  · intro n v
    exact FGProjectiveCat.freeIso_inv_apply A n v
  · intro n m b
    exact FGProjectiveCat.freeIso_matrix_square A b
  · intro x
    exact FGProjectiveCat.regularIso_hom_apply A x
  · intro z
    rfl

/-- Literal coordinate, full mixed-rank block and regular-stabilization coherence. -/
public theorem free_block_characteristic :
    let C := FiniteRowRanks A
    let E := equivalence A
    let F := fun n : ℕ => (Idempotents.toKaroubi C).obj n
    let H := fun n => freeIso A n
    let M := fun {n m : ℕ} (b : Matrix (Fin n) (Fin m) A) =>
      (Idempotents.toKaroubi C).map ((rowHomEquiv A n m).symm b)
    let B := fun n m => freeBiprodIso A n m
    let G := fun n (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) => freeAut A n g
    let S := fun n => regularSuccessorIso A n
    (∀ n m : ℕ, (B n m).hom =
      biprod.lift (M (fun (k : Fin (n + m)) (i : Fin n) =>
        if k = Fin.castAdd m i then (1 : A) else 0))
        (M (fun (k : Fin (n + m)) (j : Fin m) =>
          if k = Fin.natAdd n j then (1 : A) else 0))) ∧
    (∀ n m : ℕ, (B n m).inv =
      biprod.desc (M (fun (i : Fin n) (k : Fin (n + m)) =>
        if k = Fin.castAdd m i then (1 : A) else 0))
        (M (fun (j : Fin m) (k : Fin (n + m)) =>
          if k = Fin.natAdd n j then (1 : A) else 0))) ∧
    (∀ n m : ℕ, E.functor.mapIso (B n m) ≪≫ E.functor.mapBiprod (F n) (F m) ≪≫
      biprod.mapIso (H n) (H m) = H (n + m) ≪≫ FGProjectiveCat.standardFreeAddIso A n m) ∧
    (∀ (n : ℕ) (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ),
      (G n g).hom = M (↑(MulOpposite.unop g) : Matrix (Fin n) (Fin n) A) ∧
      (G n g).inv = M (↑((MulOpposite.unop g)⁻¹) : Matrix (Fin n) (Fin n) A) ∧
      (H n).conjAut (Aut.of (E.functor.mapIso (G n g))) =
        FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n g) ∧
    (∀ (n m : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) A)
      (h : Matrix.GeneralLinearGroup (Fin m) A),
      G (n + m) (MulOpposite.op (Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := m))
          (Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal g h))) =
        ((B n m).symm.conjAut
          (Aut.of (biprod.mapIso (G n (MulOpposite.op g))
            (G m (MulOpposite.op h))))).asIso) ∧
    (∀ (n m : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) A),
      G (n + m) (MulOpposite.op (Matrix.GeneralLinearGroup.blockStabilization n m A g)) =
        ((B n m).symm.conjAut
          (Aut.of (biprod.mapIso (G n (MulOpposite.op g))
            (Iso.refl (F m))))).asIso) ∧
    (∀ (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) A),
      G (n + 1) (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization A g)) =
        ((B n 1).symm.conjAut
          (Aut.of (biprod.mapIso (G n (MulOpposite.op g))
            (Iso.refl (F 1))))).asIso) ∧
    (∀ n : ℕ, S n = E.functor.mapIso (B n 1) ≪≫ E.functor.mapBiprod (F n) (F 1) ≪≫
      biprod.mapIso (H n) (regularIso A)) ∧
    (∀ n : ℕ, S n = H (n + 1) ≪≫ FGProjectiveCat.standardFreeAddIso A n 1 ≪≫
      biprod.mapIso (Iso.refl (FGProjectiveCat.standardFree A n))
        ((H 1).symm ≪≫ regularIso A)) ∧
    (∀ (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) A),
      (S n).conjAut (Aut.of (E.functor.mapIso
          (G (n + 1) (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization A g))))) =
        Aut.of (biprod.mapIso
          (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso
          (Iso.refl (FGProjectiveCat.regular A)))) := by
  dsimp only
  refine ⟨?_, ?_, FGProjectiveCat.freeBiprod_image A, ?_,
    FGProjectiveCat.freeAut_blockDiagonal A, FGProjectiveCat.freeAut_blockStabilization A,
    FGProjectiveCat.freeAut_stabilization A, ?_, ?_,
    FGProjectiveCat.regularSuccessor_stabilization A⟩
  · intro n m
    rfl
  · intro n m
    rfl
  · intro n g
    exact ⟨rfl, rfl, FGProjectiveCat.freeAut_characteristic A n g⟩
  · intro n
    rfl
  · intro n
    have hr : (freeIso A 1).symm ≪≫ regularIso A = FGProjectiveCat.standardRegularIso A := by
      change (FGProjectiveCat.freeIso A 1).symm ≪≫
        (FGProjectiveCat.freeIso A 1 ≪≫ FGProjectiveCat.standardRegularIso A) = _
      simp only [Iso.symm_self_id_assoc]
    rw [hr]
    exact FGProjectiveCat.regularSuccessor_image A n

end IdempotentModel

end FGProjectiveCat
