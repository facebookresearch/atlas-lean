/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.LinearHomCochainComplex

/-!
# Contravariant Hom-cochains of a chain homotopy equivalence

Let R be a ring and C a preadditive R-linear category. A chain homotopy equivalence e : K ≃ L
between complexes indexed by ℕ induces a cochain homotopy equivalence Hom_C(L, G) ≃ Hom_C(K,
G) for every G. Its forward and inverse maps are precomposition with e.hom and e.inv.

In every degree n these maps induce an isomorphism on Hom-cohomology, natural in the
coefficient object G. The construction keeps the contravariant direction in the complex
argument and the covariant direction in coefficients.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite

universe w v u

namespace HomologicalComplex.HomotopyEquiv

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {K L : ChainComplex C ℕ}

/-- Let R be a ring and C a preadditive R-linear category. Let e : HomotopyEquiv K L be a chain
homotopy equivalence between ℕ-indexed chain complexes and let G : C. It induces a cochain
homotopy equivalence Hom_C(L, G) ≃ Hom_C(K, G). The forward map is precomposition with e.hom :
K ⟶ L and the inverse is precomposition with e.inv : L ⟶ K; the two inverse homotopies come
from those of e. -/
noncomputable def mapLinearHomCochainComplex
    (e : HomotopyEquiv K L) (G : C) :
    HomotopyEquiv
      ((linearHomCochainComplexFunctor R C G).obj (op L))
      ((linearHomCochainComplexFunctor R C G).obj (op K)) where
  hom := (linearHomCochainComplexFunctor R C G).map e.hom.op
  inv := (linearHomCochainComplexFunctor R C G).map e.inv.op
  homotopyHomInvId := by
    have h := e.homotopyInvHomId.mapLinearHomCochainComplex R G
    simpa [Functor.map_comp, Functor.map_id] using h
  homotopyInvHomId := by
    have h := e.homotopyHomInvId.mapLinearHomCochainComplex R G
    simpa [Functor.map_comp, Functor.map_id] using h

/-- Let R be a ring and C a preadditive R-linear category. For a chain homotopy equivalence e : K
≃ L and n : ℕ, precomposition with e.hom gives a natural isomorphism G ↦ H^n(Hom_C(L, G)) ≅ G
↦ H^n(Hom_C(K, G)). For a coefficient map a : G ⟶ G', its components E_G satisfy H^n(Hom_C(L,
a)) ≫ E_G'.hom = E_G.hom ≫ H^n(Hom_C(K, a)). -/
noncomputable def linearHomCochainComplexHomologyNatIso
    (e : HomotopyEquiv K L) (n : ℕ) :
    HomologicalComplex.linearHomCochainComplexHomologyFunctor R C L n ≅
      HomologicalComplex.linearHomCochainComplexHomologyFunctor R C K n :=
  NatIso.ofComponents
    (fun G => (mapLinearHomCochainComplex R e G).toHomologyIso n)
    (fun {G G'} f => by
      change
        homologyMap (((linearHomCochainComplexBifunctor R C).map f).app
            (op L)) n ≫
            homologyMap (((linearHomCochainComplexBifunctor R C).obj G').map
              e.hom.op) n =
          homologyMap (((linearHomCochainComplexBifunctor R C).obj G).map
              e.hom.op) n ≫
            homologyMap (((linearHomCochainComplexBifunctor R C).map f).app
              (op K)) n
      rw [← homologyMap_comp, ← homologyMap_comp]
      exact congrArg (fun g => homologyMap g n)
        (((linearHomCochainComplexBifunctor R C).map f).naturality e.hom.op).symm)

end HomologicalComplex.HomotopyEquiv
