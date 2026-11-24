/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetCoproducts

/-!
# Tests for coproducts of simplicial sets

Consumer checks for
`MathlibExt/AlgebraicTopology/SimplicialSet/SSetCoproducts.lean`:
the coproduct element API (Sigma-type description, disjointness,
coproducts of monomorphisms), pullback squares over coproducts
(coproducts of pullbacks, universality, disjointness squares),
and coproducts of inner fibrations. This module imports only the
neutral coproduct module, proving it stands alone.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SSetCoproductsTest

/-! ### Elements of coproducts -/

/-- Degree-`0` simplices of `Δ[1] ∐ Δ[1]` are Sigma pairs, and
the component inclusions are the Sigma constructors. -/
example (y : (Δ[1] : SSet.{0}) _⦋0⦌) :
    SSet.sigmaObjEquiv (fun _ : Fin 2 => (Δ[1] : SSet.{0})) 0
        ((Sigma.ι (fun _ : Fin 2 => (Δ[1] : SSet.{0})) 0).app (op ⦋0⦌) y) =
      ⟨0, y⟩ :=
  @SSet.sigmaObjEquiv_ι_app _ (fun _ : Fin 2 => (Δ[1] : SSet.{0})) 0 0 y

example {c c' : Fin 2} {y : (Δ[1] : SSet.{0}) _⦋0⦌}
    {y' : (Δ[1] : SSet.{0}) _⦋0⦌}
    (h : (Sigma.ι (fun _ : Fin 2 => (Δ[1] : SSet.{0})) c).app (op ⦋0⦌) y =
      (Sigma.ι (fun _ : Fin 2 => (Δ[1] : SSet.{0})) c').app (op ⦋0⦌) y') :
    c = c' :=
  SSet.eq_of_sigma_ι_app_eq h

/-- The coproduct of identity maps is a monomorphism, via the
generic `MorphismProperty` coproduct stability. -/
example :
    Mono (Limits.Sigma.map fun _ : Fin 2 => 𝟙 (Δ[1] : SSet.{0})) :=
  SSet.mono_sigmaMap _ (fun _ => inferInstance)

/-- A map from a standard simplex into a coproduct factors
through a component. -/
example (f : (Δ[2] : SSet.{0}) ⟶ ∐ fun _ : Fin 2 => (Δ[3] : SSet.{0})) :
    ∃ (c : Fin 2) (β : (Δ[2] : SSet.{0}) ⟶ (Δ[3] : SSet.{0})),
      β ≫ Sigma.ι (fun _ : Fin 2 => (Δ[3] : SSet.{0})) c = f :=
  SSet.exists_sigma_ι_comp_eq f

/-! ### Pullbacks over coproducts -/

/-- Disjointness square for the constant identity family over
`Fin 2`. -/
example :
    IsPullback (Sigma.ι (fun _ : Fin 2 => (Δ[1] : SSet.{0})) 1)
      (𝟙 (Δ[1] : SSet.{0}))
      (Limits.Sigma.map fun _ : Fin 2 => 𝟙 (Δ[1] : SSet.{0}))
      (Sigma.ι (fun _ : Fin 2 => (Δ[1] : SSet.{0})) 1) :=
  SSet.isPullback_sigma_ι_sigmaMap
    (fun _ : Fin 2 => 𝟙 (Δ[1] : SSet.{0})) 1

/-! ### Coproducts of inner fibrations -/

/-- A coproduct of inner fibrations is an inner fibration. -/
example {A B : Fin 2 → SSet.{0}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, SSet.InnerFibration (q c)) :
    SSet.InnerFibration (Limits.Sigma.map q) :=
  SSet.innerFibration_sigmaMap q hq

#check SSet.sigmaObjEquiv
#check SSet.mono_sigmaMap
#check SSet.isPullback_sigmaMap
#check SSet.isPullback_sigmaDesc_fst_map_snd
#check SSet.isPullback_sigma_ι_sigmaMap
#check SSet.innerFibration_sigmaMap

#print axioms SSet.mono_sigmaMap
#print axioms SSet.innerFibration_sigmaMap
#print axioms SSet.isPullback_sigmaMap

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SSetCoproductsTest

end
