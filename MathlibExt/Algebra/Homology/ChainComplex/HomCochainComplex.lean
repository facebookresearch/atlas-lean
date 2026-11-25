/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import MathlibExt.Algebra.Homology.CochainComplex.AlternatingDifferential
public import MathlibExt.Algebra.Homology.HomComplex.Map
public meta import Lean.Elab.Tactic.Omega

/-!
# Hom cochains from a chain complex

Reindexing and `HomComplex` give full products over integer degrees.
The target-degree sign change produces unweighted precomposition and
`(-1)^(n+1)` postcomposition in the differential.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The full total Hom cochain complex in the coefficient-first source convention. -/
def homCochainComplex (P : ChainComplex C ℤ) (I : CochainComplex C ℤ) :
    CochainComplex AddCommGrpCat.{v} ℤ :=
  CochainComplex.alternatingDifferential
    (CochainComplex.HomComplex ((cochainComplexEquivalence C).functor.obj P) I)

@[simp]
theorem homCochainComplex_X (P : ChainComplex C ℤ) (I : CochainComplex C ℤ) (n : ℤ) :
    (homCochainComplex P I).X n = AddCommGrpCat.of
      (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) I n) := rfl

/-- The native-object sign comparison; its degree map is the triangular unit. -/
def homCochainComplexIso (P : ChainComplex C ℤ) (I : CochainComplex C ℤ) :
    homCochainComplex P I ≅
      CochainComplex.HomComplex ((cochainComplexEquivalence C).functor.obj P) I :=
  CochainComplex.alternatingDifferentialIso _

@[simp]
theorem homCochainComplexIso_hom_f (P : ChainComplex C ℤ) (I : CochainComplex C ℤ) (n : ℤ) :
    (homCochainComplexIso P I).hom.f n =
      Int.triangularSign n • 𝟙 ((homCochainComplex P I).X n) := rfl

/-- The source's total-Hom differential, on reindexed components. -/
theorem homCochainComplex_d_v (P : ChainComplex C ℤ) (I : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + 1 = m)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) I n)
    (p q : ℤ) (hpq : p + m = q) :
    (((homCochainComplex P I).d n m).hom z).v p q hpq =
      ((cochainComplexEquivalence C).functor.obj P).d p (p + 1) ≫
        z.v (p + 1) q (by omega) +
      m.negOnePow • (z.v p (q - 1) (by omega) ≫ I.d (q - 1) q) := by
  change (m.negOnePow • CochainComplex.HomComplex.δ n m z).v p q hpq = _
  rw [CochainComplex.HomComplex.Cochain.units_smul_v,
    CochainComplex.HomComplex.δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl,
    smul_add, smul_smul, Int.units_mul_self, one_smul, add_comm]

/-- Precomposition and postcomposition retain the variance. -/
def homCochainComplexMap {P P' : ChainComplex C ℤ} {I I' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : I ⟶ I') : homCochainComplex P I ⟶ homCochainComplex P' I' :=
  CochainComplex.alternatingDifferentialMap
    (CochainComplex.HomComplex.map ((cochainComplexEquivalence C).functor.map f) g)

/-- The map on each product component is the pre/postcomposition. -/
theorem homCochainComplexMap_v {P P' : ChainComplex C ℤ} {I I' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : I ⟶ I') (n p q : ℤ) (hpq : p + n = q)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) I n) :
    (((homCochainComplexMap f g).f n).hom z).v p q hpq =
      ((cochainComplexEquivalence C).functor.map f).f p ≫ z.v p q hpq ≫ g.f q := by
  change (CochainComplex.HomComplex.mapLinear
    ((cochainComplexEquivalence C).functor.map f) g n z).v p q hpq = _
  exact CochainComplex.HomComplex.mapLinear_v _ _ n p q hpq z

@[simp]
theorem homCochainComplexMap_id (P : ChainComplex C ℤ) (I : CochainComplex C ℤ) :
    homCochainComplexMap (𝟙 P) (𝟙 I) = 𝟙 (homCochainComplex P I) := by
  let A := CochainComplex.alternatingDifferentialFunctor (C := AddCommGrpCat.{v})
  change A.map (CochainComplex.HomComplex.map
    ((cochainComplexEquivalence C).functor.map (𝟙 P)) (𝟙 I)) = 𝟙 _
  rw [(cochainComplexEquivalence C).functor.map_id P,
    CochainComplex.HomComplex.map_id, A.map_id]

/-- Both source variables retain their contravariant/covariant composition order. -/
theorem homCochainComplexMap_comp {P P' P'' : ChainComplex C ℤ}
    {I I' I'' : CochainComplex C ℤ}
    (f : P' ⟶ P) (f' : P'' ⟶ P') (g : I ⟶ I') (g' : I' ⟶ I'') :
    homCochainComplexMap f g ≫ homCochainComplexMap f' g' =
      homCochainComplexMap (f' ≫ f) (g ≫ g') := by
  let A := CochainComplex.alternatingDifferentialFunctor (C := AddCommGrpCat.{v})
  change A.map (CochainComplex.HomComplex.map
      ((cochainComplexEquivalence C).functor.map f) g) ≫
    A.map (CochainComplex.HomComplex.map
      ((cochainComplexEquivalence C).functor.map f') g') =
    A.map (CochainComplex.HomComplex.map
      ((cochainComplexEquivalence C).functor.map (f' ≫ f)) (g ≫ g'))
  rw [← A.map_comp, CochainComplex.HomComplex.map_comp,
    (cochainComplexEquivalence C).functor.map_comp f' f]

end ChainComplex
