/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.CofaceComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodementCupProduct

/-! # Original Godement cup clients of coface comparison transport -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC s
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

open MonoidalCategory
open scoped BigOperators TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

universe u w

/-- The actual comparison from the original Godement sections complex, using the
existing alternating-sections isomorphism and the literal coface map. -/
def smallEtaleGodementCofaceComparisonMap (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {A : CosimplicialObject AddCommGrpCat.{max u w}}
    (a : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X F) A) :
    smallEtaleGodementSectionsComplex.{u, w} X F ⟶
      AlternatingCofaceMapComplex.obj A :=
  (smallEtaleGodementAlternatingSectionsIso.{u, w} X F).inv ≫ a.alternatingMap

set_option backward.isDefEq.respectTransparency.types false in
/-- Every component is the given degree morphism on the original sections. -/
theorem smallEtaleGodementCofaceComparisonMap_f (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {A : CosimplicialObject AddCommGrpCat.{max u w}}
    (a : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X F) A) (n : ℕ) :
    (smallEtaleGodementCofaceComparisonMap.{u, w} X F a).f n = a.app n := by
  change 𝟙 _ ≫ a.app n = a.app n
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
/-- The original Godement cup is preserved by genuine coface and degree tensor
comparisons. Its actual front/back maps are used on the same original sections. -/
theorem smallEtaleGodementCochainCup_cofaceComparison (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {A B D : CosimplicialObject AddCommGrpCat.{max u w}}
    (a : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X F) A)
    (b : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X G) B)
    (c : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X
        (smallEtaleTensorSheaf.{u, w} X F G)) D)
    (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
      D.obj (SimplexCategory.mk n))
    (hm : ∀ n, (a.app n ⊗ₘ b.app n) ≫ m n =
      smallEtaleGodementSectionsDegreePairing.{u, w} X F G n ≫ c.app n)
    (p q : ℕ) :
    smallEtaleGodementCochainCup.{u, w} X F G p q ≫ c.app (p + q) =
      (a.app p ⊗ₘ b.app q) ≫ CosimplicialCup.awPair A B D m p q (p + q) rfl := by
  exact (CosimplicialCup.awPair_cofaceComparison a b c
    (smallEtaleGodementSectionsDegreePairing.{u, w} X F G) m hm p q (p + q) rfl).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- On original pure cochains, the actual comparison gives exactly the target
front and back values followed by the actual degree tensor pairing. -/
theorem smallEtaleGodementCochainCup_cofaceComparison_tmul (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {A B D : CosimplicialObject AddCommGrpCat.{max u w}}
    (a : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X F) A)
    (b : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X G) B)
    (c : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X
        (smallEtaleTensorSheaf.{u, w} X F G)) D)
    (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
      D.obj (SimplexCategory.mk n))
    (hm : ∀ n, (a.app n ⊗ₘ b.app n) ≫ m n =
      smallEtaleGodementSectionsDegreePairing.{u, w} X F G n ≫ c.app n)
    (p q : ℕ) (x : (smallEtaleGodementSectionsComplex.{u, w} X F).X p)
    (y : (smallEtaleGodementSectionsComplex.{u, w} X G).X q) :
    (c.app (p + q)).hom
        ((smallEtaleGodementCochainCup.{u, w} X F G p q).hom (x ⊗ₜ[ℤ] y)) =
      (m (p + q)).hom
        ((A.map (AlexanderWhitney.frontInclusion p q (p + q) rfl)).hom ((a.app p).hom x) ⊗ₜ[ℤ]
          (B.map (AlexanderWhitney.backInclusion p q (p + q) rfl)).hom ((b.app q).hom y)) := by
  have h := ConcreteCategory.congr_hom
    (smallEtaleGodementCochainCup_cofaceComparison.{u, w} X F G a b c m hm p q)
    (x ⊗ₜ[ℤ] y)
  change (c.app (p + q)).hom
      ((smallEtaleGodementCochainCup.{u, w} X F G p q).hom (x ⊗ₜ[ℤ] y)) =
    (m (p + q)).hom
      (TensorProduct.map
        (A.map (AlexanderWhitney.frontInclusion p q (p + q) rfl)).hom.toIntLinearMap
        (B.map (AlexanderWhitney.backInclusion p q (p + q) rfl)).hom.toIntLinearMap
        (TensorProduct.map (a.app p).hom.toIntLinearMap (b.app q).hom.toIntLinearMap
          (x ⊗ₜ[ℤ] y))) at h
  simpa only [TensorProduct.map_tmul, AddMonoidHom.coe_toIntLinearMap] using h

set_option backward.isDefEq.respectTransparency.types false in
/-- The same actual comparison preserves the original native Godement homology
cup. The target pairing enters through its literal AW component formula. -/
theorem smallEtaleGodementHomologyCup_cofaceComparison (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {A B D : CosimplicialObject AddCommGrpCat.{max u w}}
    (a : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X F) A)
    (b : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X G) B)
    (c : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X
        (smallEtaleTensorSheaf.{u, w} X F G)) D)
    (Q : HomologicalComplex.CochainGradedPairing
      (AlternatingCofaceMapComplex.obj A) (AlternatingCofaceMapComplex.obj B)
      (AlternatingCofaceMapComplex.obj D))
    (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
      D.obj (SimplexCategory.mk n))
    (hQ : ∀ p q, Q.pair p q = CosimplicialCup.awPair A B D m p q (p + q) rfl)
    (hm : ∀ n, (a.app n ⊗ₘ b.app n) ≫ m n =
      smallEtaleGodementSectionsDegreePairing.{u, w} X F G n ≫ c.app n)
    (p q : ℕ) :
    (HomologicalComplex.homologyMap (smallEtaleGodementCofaceComparisonMap.{u, w} X F a) p ⊗ₘ
        HomologicalComplex.homologyMap (smallEtaleGodementCofaceComparisonMap.{u, w} X G b) q) ≫
        Q.pairHomology p q =
      smallEtaleGodementHomologyCup.{u, w} X F G p q ≫
        HomologicalComplex.homologyMap
          (smallEtaleGodementCofaceComparisonMap.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G) c)
          (p + q) := by
  apply HomologicalComplex.CochainGradedPairing.pairHomology_naturality
    (smallEtaleGodementGradedPairing.{u, w} X F G) Q
    (smallEtaleGodementCofaceComparisonMap.{u, w} X F a)
    (smallEtaleGodementCofaceComparisonMap.{u, w} X G b)
    (smallEtaleGodementCofaceComparisonMap.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G) c)
  intro i j
  rw [smallEtaleGodementGradedPairing_pair.{u, w} X F G i j,
    smallEtaleGodementCofaceComparisonMap_f, smallEtaleGodementCofaceComparisonMap_f,
    smallEtaleGodementCofaceComparisonMap_f, hQ i j]
  exact smallEtaleGodementCochainCup_cofaceComparison.{u, w} X F G a b c m hm i j

end AlgebraicGeometry.Scheme.DerivedSections
