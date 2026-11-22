/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPointFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMonoRight
import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration

/-!
# The original interval endpoints are not marked mono-right maps

Both whole maximally marked endpoint inclusions over the point are
monomorphisms. Each misses the other original vertex. The actual marked
slice monomorphism right class forces all native boundary lifts, hence
vertex surjectivity; consequently neither original endpoint map belongs
to that right class. No weak-class or marked-model outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Both original maximally marked point endpoint inclusions remain monic in the original marked slice. -/
theorem pointEndpoint_mono (ε : Fin 2) : Mono (pointEndpoint.{u} ε) := by
  let _ : Mono (maximal.map (SSet.stdSimplex.{u}.δ ε)).hom := inferInstanceAs (Mono (SSet.stdSimplex.δ ε))
  let _ : Mono (maximal.map (SSet.stdSimplex.{u}.δ ε)) := Hom.mono_of_underlying _
  let _ : Mono (pointEndpoint.{u} ε).left := inferInstanceAs (Mono (maximal.map (SSet.stdSimplex.{u}.δ ε)))
  exact Over.mono_of_mono_left (pointEndpoint.{u} ε)

/-- The original native endpoint misses its other original vertex in every value universe. -/
theorem pointEndpoint_not_surjective_zero (ε : Fin 2) :
    ¬ Function.Surjective ((pointEndpoint.{u} ε).left.hom.app (op ⦋0⦌)) := by
  intro h
  obtain ⟨x, hx⟩ := h (SSet.stdSimplex.obj₀Equiv.symm ε)
  let a : (Δ[0] : SSet.{u}) _⦋0⦌ := x
  have he := congrArg (fun y : (Δ[1] : SSet.{u}) _⦋0⦌ => y 0) hx
  change ε.succAbove (a 0) = ε at he
  exact Fin.succAbove_ne ε (a 0) he

/-- Neither whole original maximally marked endpoint has the genuine monomorphism right lifting class. -/
theorem pointEndpoint_not_monoRight (ε : Fin 2) :
    ¬ (monomorphisms (Over (max (Δ[0] : SSet.{u})))).rlp (pointEndpoint.{u} ε) := by
  intro h
  have hM := (over_monomorphisms_rlp_iff (pointEndpoint.{u} ε)).mp h
  have hU := (monomorphisms_rlp_iff (pointEndpoint.{u} ε).left).mp hM
  have hI : modelCategoryQuillen.I.{u}.rlp (pointEndpoint.{u} ε).left.hom := by
    rw [← rlp_monomorphisms]
    exact hU.1
  apply pointEndpoint_not_surjective_zero ε
  intro y
  exact exists_vertex_lift_of_rlp_I hI y

end SSet.Marked
