/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex

/-!
# Original simplex linearization and signed BK total clients

The actual bidegree objects and maps retain each original bisimplex.
Both alternating differentials and both fixed total-complex signs are
visible on the same original summand inclusions.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe t uJ vJ uA vA

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKTotalTests

/-- Generic pointwise linearization retains the original bisimplices in an
arbitrary simplicial and coefficient-category universe frame. -/
theorem originalGenericLinearization (A : Type uA) [Category.{vA} A]
    [HasCoproducts.{t} A] (R : A) (B : SimplicialObject SSet.{t}) (p q : ℕ) :
    (((SSet.bisimplicialLinearizationFunctor A R).obj B).obj (op ⦋p⦌)).obj (op ⦋q⦌) =
      ∐ fun _ : (B.obj (op ⦋p⦌)).obj (op ⦋q⦌) => R :=
  SSet.bisimplicialLinearizationFunctor_obj_obj_obj A R B p q

variable {J : Type uJ} [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max uJ vJ} A] (R : A)
variable {D E : J ⥤ SSet.{max uJ vJ}}

/-- The actual bidegree map sends each original simplex-indexed copy of the
coefficient to the copy indexed by the original bisimplicial map. -/
theorem originalBidegreeSummandMap (α : D ⟶ E) (p q : ℕ)
    (x : ((SSet.bkBarBisimplicial D).obj (op ⦋p⦌)).obj (op ⦋q⦌)) :
    Sigma.ι (fun _ : ((SSet.bkBarBisimplicial D).obj (op ⦋p⦌)).obj (op ⦋q⦌) => R) x ≫
        (((SSet.bkAlternatingBicomplexFunctor A R).map α).f p).f q =
      Sigma.ι (fun _ : ((SSet.bkBarBisimplicial E).obj (op ⦋p⦌)).obj (op ⦋q⦌) => R)
        ((((SSet.bkBarBisimplicialFunctor (J := J)).map α).app (op ⦋p⦌)).app (op ⦋q⦌) x) := by
  change Sigma.ι (fun _ : ((SSet.bkBarBisimplicial D).obj (op ⦋p⦌)).obj
      (op ⦋q⦌) => R) x ≫ (sigmaConst.obj R).map _ = _
  simp [sigmaConst]

/-- Both original integer alternating face sums are retained in every
bidegree of the same original bicomplex. -/
theorem originalAlternatingFaces (D : J ⥤ SSet.{max uJ vJ}) (p q : ℕ) :
    let B := (SSet.bisimplicialLinearizationFunctor A R).obj (SSet.bkBarBisimplicial D)
    let K := SSet.bkAlternatingBicomplex A R D
    (K.X p).d (q + 1) q =
        ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • (B.obj (op ⦋p⦌)).δ i ∧
      (K.d (p + 1) p).f q =
        ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (B.δ i).app (op ⦋q⦌) :=
  ⟨AlgebraicTopology.bisimplicialAlternatingBicomplex_vertical_d_eq_sum A _ p q,
    AlgebraicTopology.bisimplicialAlternatingBicomplex_horizontal_d_f_eq_sum A _ p q⟩

section Total

variable [HasCountableCoproducts A]

/-- The original signed total map preserves the degree-p+q summand inclusion. -/
theorem originalTotalMap (α : D ⟶ E) (p q : ℕ) :
    SSet.bkAlternatingTotalι A R D p q ≫
        ((SSet.bkAlternatingTotalComplexFunctor A R).map α).f (p + q) =
      (((SSet.bkAlternatingBicomplexFunctor A R).map α).f p).f q ≫
        SSet.bkAlternatingTotalι A R E p q :=
  HomologicalComplex₂.ιTotal_map
    (SSet.bkAlternatingBicomplex A R D) (SSet.bkAlternatingBicomplex A R E)
    ((SSet.bkAlternatingBicomplexFunctor A R).map α) (.down ℕ) p q (p + q) rfl

/-- The actual total differential on one original summand is the horizontal
plus vertical differential with the fixed original epsilon signs. -/
theorem originalSignedTotalDifferential (D : J ⥤ SSet.{max uJ vJ}) (p q : ℕ) :
    let K := SSet.bkAlternatingBicomplex A R D
    SSet.bkAlternatingTotalι A R D (p + 1) (q + 1) ≫
        (SSet.bkAlternatingTotalComplex A R D).d ((p + 1) + (q + 1)) (p + q + 1) =
      ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q + 1) •
        ((K.d (p + 1) p).f (q + 1) ≫
          K.ιTotalOrZero (.down ℕ) p (q + 1) (p + q + 1)) +
      ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q + 1) •
        ((K.X (p + 1)).d (q + 1) q ≫
          K.ιTotalOrZero (.down ℕ) (p + 1) q (p + q + 1)) := by
  let K := SSet.bkAlternatingBicomplex A R D
  change K.ιTotal (.down ℕ) (p + 1) (q + 1) ((p + 1) + (q + 1)) rfl ≫
      (K.total (.down ℕ)).d ((p + 1) + (q + 1)) (p + q + 1) = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  exact congrArg₂ (fun f g => f + g)
    (HomologicalComplex₂.d₁_eq' K (.down ℕ) (i₁' := p) rfl (q + 1) (p + q + 1))
    (HomologicalComplex₂.d₂_eq' K (.down ℕ) (p + 1) (i₂' := q) rfl (p + q + 1))

end Total

end MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKTotalTests

end
