/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BranchIdeal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

/-- `exactSource` consumer with the original binders. -/
example {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) (U : X.affineOpens)
    (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {ξ}, isClosed_closure⟩).ideal U) =
      Scheme.branchIdeal h :=
  Scheme.IdealSheafData.map_germ_vanishingIdeal_closure_eq_branchIdeal h U hx

/-- Higher-universe consumer. -/
example {X : Scheme.{u + 1}} {ξ x : X} (h : ξ ⤳ x) (U : X.affineOpens)
    (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {ξ}, isClosed_closure⟩).ideal U) =
      Scheme.branchIdeal h :=
  Scheme.IdealSheafData.map_germ_vanishingIdeal_closure_eq_branchIdeal h U hx

/-- The branch ideal is prime, so the specialization hypothesis produces a
genuine prime of the stalk rather than an arbitrary ideal. -/
example {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) : (Scheme.branchIdeal h).IsPrime :=
  AlgebraicGeometry.Scheme.branchIdeal_isPrime h
