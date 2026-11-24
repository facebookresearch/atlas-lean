/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.LinearHomCochainComplex

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite

universe w v u

namespace HomologicalComplex.HomotopyEquiv

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {K L : ChainComplex C ℕ}

/-- Linear `Hom(-, G)` carries a chain-homotopy equivalence to a cochain
homotopy equivalence. -/
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

/-- A chain-homotopy equivalence induces an isomorphism on linear
Hom-cohomology, natural in the coefficient object. -/
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
