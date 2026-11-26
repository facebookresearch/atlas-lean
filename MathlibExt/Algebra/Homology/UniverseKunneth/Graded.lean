/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.UniverseTensorExactness
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyAdapter
public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import Mathlib.Algebra.Homology.SingleHomology
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.Algebra.Homology.GradedHomology.Monoidal

/-!
# Graded cycle Künneth maps over a commutative ring

Let R be a commutative ring in universe u, and choose the common coefficient universe
W=max(u,v), with v independent of u. For nonnegative chain complexes K,L, a pair of cycles in
degrees p,q tensors into a cycle in degree p+q of K⊗_R L. The tensor differential is
d(x⊗y)=dx⊗y+(-1)^p x⊗dy. Passing to homology gives κ_{p,q}:H_pK⊗H_qL→H_{p+q}(K⊗L).

The maps κ_{p,q}, summed over p+q=n, define μ:H(K)⊗H(L)→H(K⊗L) on ℕ-graded homology. Both the
bidegree pairing and μ are natural in the two complexes. The tensor unit, concentrated in degree
zero, gives a canonical isomorphism from the graded tensor unit to its graded homology and the
corresponding unit map. These constructions hold over any commutative ring.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.UniverseKunneth

variable {R : Type u} [CommRing R]


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. This functor sends an R-linear chain complex K of shape down ℕ to the
ℕ-graded module H(K), with component H_nK in degree n. A chain map f is sent to the family
H_n(f). Both complex terms and homology modules lie in W; the scalar ring remains R. -/
abbrev homologyFunctor : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) ⥤ (GradedObject ℕ
  (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R)) := gradedHomologyFunctor
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) (ComplexShape.down ℕ)

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. For chain complexes K,L of shape down ℕ and p,q∈ℕ, this is κ_{p,q}:H_pK⊗_R
H_qL→H_{p+q}(K⊗_R L). It sends the tensor of cycle classes [x]⊗[y] to the class of x⊗y in the
(p,q) summand of the tensor complex, and is the descent of that cycle tensor map. -/
abbrev pair (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q : ℕ) :
    K.homology p ⊗ L.homology q ⟶ (K ⊗ L).homology (p + q) :=
  ChainGradedPairing.pairHomology (𝟙 (K ⊗ L))
    (ChainGradedPairing.homologyDescentData (𝟙 (K ⊗ L))) p q

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. For chain complexes K,L of shape down ℕ, this graded map
μ:H(K)⊗H(L)→H(K⊗L) has degree-n source the coproduct of H_pK⊗H_qL over p+q=n. Its restriction to
each such summand is the canonical homology pairing κ_{p,q}, followed by the identification of
the homology degree p+q with n. -/
def tensorator (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :
    homologyFunctor.obj K ⊗ homologyFunctor.obj L ⟶ homologyFunctor.obj (K ⊗ L) :=
  HomologicalComplex.GradedHomology.tensorator K L

@[reassoc (attr := simp)]
theorem ι_tensorator (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q n : ℕ) (h : p
  + q = n) :
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K) (homologyFunctor.obj L)
      p q n h ≫ tensorator K L n =
      pair K L p q ≫ (homologyIsoOfEq (K ⊗ L) h).hom :=
  HomologicalComplex.GradedHomology.ι_tensorator K L p q n h

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. For chain maps f:K→K′ and g:L→L′ of shape down ℕ and p,q∈ℕ, the cycle
pairings satisfy (H_p(f)⊗H_q(g))≫κ_{K′,L′}^{p,q}=κ_{K,L}^{p,q}≫H_{p+q}(f⊗g). Both sides map
H_pK⊗H_qL to H_{p+q}(K′⊗L′). -/
@[reassoc]
theorem pair_naturality {K L K' L' : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)} (f : K ⟶
  K') (g : L ⟶ L') (p q : ℕ) :
    (homologyMap f p ⊗ₘ homologyMap g q) ≫ pair K' L' p q =
      pair K L p q ≫ homologyMap (f ⊗ₘ g) (p + q) := by
  exact HomologicalComplex.GradedHomology.pair_naturality f g p q


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. For chain maps f:K→K′ and g:L→L′ of shape down ℕ and graded homology H,
the tensorators satisfy (H(f)⊗H(g))≫μ_{K′,L′}=μ_{K,L}≫H(f⊗g). This is the degreewise assembly of
the bidegree pairing naturality equations. -/
@[reassoc]
theorem tensorator_naturality {K L K' L' : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)} (f
  : K ⟶ K') (g : L ⟶ L') :
    (homologyFunctor.map f ⊗ₘ homologyFunctor.map g) ≫ tensorator K' L' =
      tensorator K L ≫ homologyFunctor.map (f ⊗ₘ g) := by
  exact HomologicalComplex.GradedHomology.tensorator_naturality f g


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. The chain tensor unit is concentrated in degree zero at the module tensor
unit. Its graded homology therefore has the same degree-zero term and zero positive-degree
terms. This is the canonical isomorphism 𝟙_{graded}≅H(𝟙_{chain}), with degree-zero component the
inverse single-complex homology comparison. -/
def unitIso : 𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R)) ≅ homologyFunctor.obj (𝟙_
  (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitIso (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. This map e:𝟙_{graded}→H(𝟙_{chain}) is the forward morphism of the
canonical unit homology isomorphism. In degree zero it maps the coefficient tensor unit to the
homology of the single unit complex; all positive-degree components have zero source. -/
def unitMap : 𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R)) ⟶ homologyFunctor.obj (𝟙_
  (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitMap (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

@[simp]
theorem unitMap_zero : unitMap.{u,v} (R := R) 0 =
    (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))).hom ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.UniverseScalarRestriction.Modules.{u,v}
        R))).inv := by
  exact HomologicalComplex.GradedHomology.unitMap_zero (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

instance unitMap_isIso : IsIso (unitMap.{u,v} (R := R)) := by
  exact HomologicalComplex.GradedHomology.unitMap_isIso (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

end HomologicalComplex.UniverseKunneth
