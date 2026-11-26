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

/-!
# Transporting Godement cup products through coface comparisons

Let X be a scheme and F,G small-étale additive-group sheaves of height max(u,w). A
coface-compatible comparison of each Godement sections cosimplicial object gives a map of
alternating cochain complexes with the prescribed degree components.

If three such comparisons intertwine the degreewise Godement tensor pairing with maps m_n :
A_n⊗B_n → D_n, then the Godement cup agrees with the target front/back Alexander–Whitney
pairing. If that target pairing is a cochain graded pairing, the equality descends to
cohomology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC s
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

open MonoidalCategory
open scoped BigOperators TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

universe u w

/-- Let X be a scheme, F an additive-group small-étale sheaf of height max(u,w), A a cosimplicial
additive-group object, and a a CofaceComparison from the Godement sections object to A. The
Godement sections cochain complex maps to the alternating coface complex of A by the inverse
alternating-sections isomorphism followed by a.alternatingMap. -/
def smallEtaleGodementCofaceComparisonMap (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {A : CosimplicialObject AddCommGrpCat.{max u w}}
    (a : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X F) A) :
    smallEtaleGodementSectionsComplex.{u, w} X F ⟶
      AlternatingCofaceMapComplex.obj A :=
  (smallEtaleGodementAlternatingSectionsIso.{u, w} X F).inv ≫ a.alternatingMap

set_option backward.isDefEq.respectTransparency.types false in
/-- For a scheme X, sheaf F, and coface comparison a from its Godement sections cosimplicial
object to A, the nth component of smallEtaleGodementCofaceComparisonMap equals a.app(n). This
holds for every n∈ℕ. -/
theorem smallEtaleGodementCofaceComparisonMap_f (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {A : CosimplicialObject AddCommGrpCat.{max u w}}
    (a : CosimplicialCup.CofaceComparison
      (smallEtaleGodementSectionsCosimplicial.{u, w} X F) A) (n : ℕ) :
    (smallEtaleGodementCofaceComparisonMap.{u, w} X F a).f n = a.app n := by
  change 𝟙 _ ≫ a.app n = a.app n
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme, F,G sheaves, and a,b,c coface comparisons from their Godement sections and
the tensor-sheaf sections to A,B,D. Suppose m_n : A_n⊗B_n → D_n satisfies
(a_n⊗b_n)≫m_n=GodementPair_n≫c_n for every n. Then Cup_God,p,q≫c_{p+q}=(a_p⊗b_q)≫AW_m,p,q,
where the target pairing uses the front and back inclusions into degree p+q. -/
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
/-- For a scheme X, coface comparisons a,b,c and degree maps m satisfying
(a_n⊗b_n)≫m_n=GodementPair_n≫c_n, let x,y be source cochains of degrees p,q. Their Godement
cup under c_{p+q} equals m_{p+q}(A(frontInclusion)(a_p x)⊗_ℤ B(backInclusion)(b_q y)). The
front vertices are 0..p and the back vertices p..p+q. -/
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
/-- Let X be a scheme, F,G additive-group sheaves of height max(u,w), and a,b,c coface comparisons
into A,B,D. Let m_n : A_n⊗B_n → D_n satisfy (a_n⊗b_n)≫m_n=GodementDegreePair_n≫c_n. If Q is a
cochain graded pairing of the alternating complexes with Q.pair(p,q)=AW_m,p,q for all p,q,
then H^p(a)⊗H^q(b) followed by Q.pairHomology equals the Godement cohomology cup followed by
H^{p+q}(c). -/
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
