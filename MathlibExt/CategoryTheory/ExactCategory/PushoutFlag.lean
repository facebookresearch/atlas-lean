/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.ExactCategory.Basic
import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty

/-!
# Completing an exact pushout flag

Let `C` be an additive exact category. Given admissible exact sequences
`K → A → X` and `A → Y → Q`, a pushout of `p : A → X` and
`r : A → Y` completes the flag to admissible exact sequences
`K → Y → P` and `X → P → Q`. The quotient map from `P` to `Q`
is characterized by zero on `X → P` and by the original quotient on `Y → P`.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- In an additive exact category `C`, let `P` be a pushout of
`p : A → X` and `r : A → Y`, with legs `x : X → P`, `y : Y → P`.
For `q : Y → Q` satisfying `r ≫ q = 0`, the induced map `P → Q`
is uniquely characterized by `x ≫ map = 0` and `y ≫ map = q`. -/
noncomputable def pushoutQuotientMap
    {A X Y P Q : C} (p : A ⟶ X) (r : A ⟶ Y) (q : Y ⟶ Q)
    (x : X ⟶ P) (y : Y ⟶ P) (wr : r ≫ q = 0)
    (sq : IsPushout p r x y) : P ⟶ Q :=
  sq.desc (0 : X ⟶ Q) q (by simp [wr])

/-- For the pushout of `p : A → X`, `r : A → Y` in an additive exact
category `C` and a map `q : Y → Q` with `r ≫ q = 0`, the induced
quotient map `P → Q` has zero composite with the pushout leg `x : X → P`. -/
@[reassoc (attr := simp)]
theorem pushoutQuotientMap_x
    {A X Y P Q : C} (p : A ⟶ X) (r : A ⟶ Y) (q : Y ⟶ Q)
    (x : X ⟶ P) (y : Y ⟶ P) (wr : r ≫ q = 0)
    (sq : IsPushout p r x y) :
    x ≫ pushoutQuotientMap p r q x y wr sq = 0 := by
  unfold pushoutQuotientMap
  exact sq.inl_desc _ _ _

/-- For the pushout of `p : A → X`, `r : A → Y` in an additive exact
category `C` and `q : Y → Q` with `r ≫ q = 0`, the induced
quotient map restricts on `y : Y → P` to `q`: `y ≫ map = q`. -/
@[reassoc (attr := simp)]
theorem pushoutQuotientMap_y
    {A X Y P Q : C} (p : A ⟶ X) (r : A ⟶ Y) (q : Y ⟶ Q)
    (x : X ⟶ P) (y : Y ⟶ P) (wr : r ≫ q = 0)
    (sq : IsPushout p r x y) :
    y ≫ pushoutQuotientMap p r q x y wr sq = q := by
  unfold pushoutQuotientMap
  exact sq.inr_desc _ _ _

variable [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- In an additive exact category `C`, suppose `K → A → X` and
`A → Y → Q` are admissible exact and `P` is a pushout with
`p ≫ x = r ≫ y`. Then the composite `K → A → Y` followed by
`y : Y → P` gives an admissible exact sequence `K → Y → P`. -/
theorem isAdmissibleExact_comp_pushout
    {K A X Y P Q : C} (i : K ⟶ A) (p : A ⟶ X) (r : A ⟶ Y)
    (q : Y ⟶ Q) (x : X ⟶ P) (y : Y ⟶ P)
    (wi : i ≫ p = 0) (wr : r ≫ q = 0)
    (hL : IsAdmissibleExact (ShortComplex.mk i p wi))
    (hR : IsAdmissibleExact (ShortComplex.mk r q wr))
    (sq : IsPushout p r x y) :
    IsAdmissibleExact
      (ShortComplex.mk (i ≫ r) y (by
        rw [Category.assoc, ← sq.w, ← Category.assoc, wi, zero_comp])) := by
  let wFlag : (i ≫ r) ≫ y = 0 := by
    rw [Category.assoc, ← sq.w, ← Category.assoc, wi, zero_comp]
  change IsAdmissibleExact (ShortComplex.mk (i ≫ r) y wFlag)
  have hir : IsAdmissibleMono (i ≫ r) :=
    admissibleMono_comp.comp_mem i r (isAdmissibleMono_f hL)
      (isAdmissibleMono_f hR)
  let hcL := isColimit_cokernelCofork_of_isAdmissibleExact hL
  let : Epi p := IsAdmissibleEpi.epi (isAdmissibleEpi_g hL)
  let gx {W : C} (g : Y ⟶ W) (hg : (i ≫ r) ≫ g = 0) : X ⟶ W :=
    hcL.desc (CokernelCofork.ofπ (r ≫ g) (by
      rw [← Category.assoc, hg]))
  have gx_fac {W : C} (g : Y ⟶ W) (hg : (i ≫ r) ≫ g = 0) :
      p ≫ gx g hg = r ≫ g := by
    change p ≫ hcL.desc (CokernelCofork.ofπ (r ≫ g) _) = r ≫ g
    exact Cofork.IsColimit.π_desc hcL
  let d {W : C} (g : Y ⟶ W) (hg : (i ≫ r) ≫ g = 0) : P ⟶ W :=
    sq.desc (gx g hg) g (gx_fac g hg)
  refine isAdmissibleExact_of_isAdmissibleMono_isColimit hir
    (CokernelCofork.IsColimit.ofπ y wFlag (fun g hg => d g hg) ?_ ?_)
  · intro W g hg
    change y ≫ sq.desc (gx g hg) g (gx_fac g hg) = g
    exact sq.inr_desc _ _ _
  · intro W g hg m hm
    change m = sq.desc (gx g hg) g (gx_fac g hg)
    apply sq.hom_ext
    · rw [← cancel_epi p]
      calc
        p ≫ (x ≫ m) = (p ≫ x) ≫ m := (Category.assoc _ _ _).symm
        _ = (r ≫ y) ≫ m := by rw [sq.w]
        _ = r ≫ (y ≫ m) := Category.assoc _ _ _
        _ = r ≫ g := by rw [hm]
        _ = p ≫ gx g hg := (gx_fac g hg).symm
        _ = p ≫ (x ≫ sq.desc (gx g hg) g (gx_fac g hg)) := by
          rw [sq.inl_desc]
    · exact hm.trans (sq.inr_desc _ _ _).symm

/-- In an additive exact category `C`, suppose `A → Y → Q` is
admissible exact and `P` is the pushout of `A → X` and `A → Y`.
The leg `X → P` followed by the induced quotient `P → Q` gives
an admissible exact sequence `X → P → Q`. -/
theorem isAdmissibleExact_pushoutQuotientMap
    {A X Y P Q : C} (p : A ⟶ X) (r : A ⟶ Y) (q : Y ⟶ Q)
    (x : X ⟶ P) (y : Y ⟶ P) (wr : r ≫ q = 0)
    (hR : IsAdmissibleExact (ShortComplex.mk r q wr))
    (sq : IsPushout p r x y) :
    IsAdmissibleExact
      (ShortComplex.mk x (pushoutQuotientMap p r q x y wr sq)
        (pushoutQuotientMap_x p r q x y wr sq)) := by
  let m : P ⟶ Q := pushoutQuotientMap p r q x y wr sq
  let wm : x ≫ m = 0 := pushoutQuotientMap_x p r q x y wr sq
  change IsAdmissibleExact (ShortComplex.mk x m wm)
  have hx : IsAdmissibleMono x :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := admissibleMonosOf C IsAdmissibleExact) sq
        (isAdmissibleMono_f hR)
  let hcR := isColimit_cokernelCofork_of_isAdmissibleExact hR
  let gq {W : C} (g : P ⟶ W) (hg : x ≫ g = 0) : Q ⟶ W :=
    hcR.desc (CokernelCofork.ofπ (y ≫ g) (by
      calc
        r ≫ (y ≫ g) = (r ≫ y) ≫ g := (Category.assoc _ _ _).symm
        _ = (p ≫ x) ≫ g := by rw [sq.w]
        _ = p ≫ (x ≫ g) := Category.assoc _ _ _
        _ = 0 := by rw [hg, comp_zero]))
  have gq_fac {W : C} (g : P ⟶ W) (hg : x ≫ g = 0) :
      q ≫ gq g hg = y ≫ g := by
    change q ≫ hcR.desc (CokernelCofork.ofπ (y ≫ g) _) = y ≫ g
    exact Cofork.IsColimit.π_desc hcR
  refine isAdmissibleExact_of_isAdmissibleMono_isColimit hx
    (CokernelCofork.IsColimit.ofπ m wm (fun g hg => gq g hg) ?_ ?_)
  · intro W g hg
    apply sq.hom_ext
    · calc
        x ≫ (m ≫ gq g hg) = (x ≫ m) ≫ gq g hg :=
          (Category.assoc _ _ _).symm
        _ = 0 := by rw [wm, zero_comp]
        _ = x ≫ g := hg.symm
    · calc
        y ≫ (m ≫ gq g hg) = (y ≫ m) ≫ gq g hg :=
          (Category.assoc _ _ _).symm
        _ = q ≫ gq g hg := by
          rw [show y ≫ m = q from pushoutQuotientMap_y p r q x y wr sq]
        _ = y ≫ g := gq_fac g hg
  · intro W g hg n hn
    apply Cofork.IsColimit.hom_ext hcR
    calc
      q ≫ n = (y ≫ m) ≫ n := by
        rw [show y ≫ m = q from pushoutQuotientMap_y p r q x y wr sq]
      _ = y ≫ (m ≫ n) := Category.assoc _ _ _
      _ = y ≫ g := by rw [hn]
      _ = q ≫ gq g hg := (gq_fac g hg).symm

end CategoryTheory.ExactCategory
