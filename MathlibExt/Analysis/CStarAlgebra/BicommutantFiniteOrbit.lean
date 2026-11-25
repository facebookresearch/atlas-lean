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

public import MathlibExt.Analysis.CStarAlgebra.BicommutantCyclicOrbit
public import MathlibExt.Analysis.CStarAlgebra.FiniteCoordinateBicommutant

/-!
# Original finite vector families lie in the actual closed source orbit

Literal finite diagonal amplification preserves original double-commutant
membership. The actual full-H cyclic orbit theorem then applies on that
finite l² carrier. Its original amplified orbit is exactly the range of
the original source algebra acting on those same coordinates; this range
is a complex submodule. Thus the closed linear orbit is the norm closure
of the literal source orbit. No amplified model, basis, projection or
closure certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Analysis.CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Simultaneous approximation of finitely many vectors.** Let `H` be a complete complex Hilbert space
and `S` a unital complex star subalgebra of the bounded operators on `H`. If `T` belongs to the
bicommutant of `S`, then for every `n ∈ ℕ` and family `ξ : Fin n → H`, the tuple `(Tξᵢ)ᵢ` belongs to
the norm closure of `{(aξᵢ)ᵢ : a ∈ S}` in the Hilbert direct sum of `n` copies of `H`. The empty
tuple is allowed. -/
theorem bicommutant_finiteOrbit_mem_closure (n : ℕ)
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) (ξ : Fin n → H) :
    (WithLp.toLp 2 (fun i : Fin n => T (ξ i)) : PiLp 2 (fun _ : Fin n => H)) ∈
      closure (Set.range fun a : S =>
        (WithLp.toLp 2 (fun i : Fin n => (a : H →L[ℂ] H) (ξ i)) : PiLp 2 (fun _ : Fin n => H))) := by
  classical
  let V := PiLp 2 (fun _ : Fin n => H)
  let d := finiteCoordinateStarAlgHom (H := H) n
  let F := d.comp S.subtype
  let Q := F.range
  let η : V := WithLp.toLp 2 ξ
  let Φ : S →ₗ[ℂ] V := (ContinuousLinearMap.apply ℂ V η).toLinearMap.comp F.toLinearMap
  have hdouble : d T ∈ Set.centralizer (Set.centralizer (Q : Set (V →L[ℂ] V))) :=
    finiteCoordinateStarAlgHom_mem_bicommutant n S T hT
  have hOrbit := bicommutant_apply_mem_cyclicOrbitSubspace Q (d T) hdouble η
  have hOrbitRange : Set.range (fun a : Q => (a : V →L[ℂ] V) η) = (LinearMap.range Φ : Set V) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      refine ⟨b, ?_⟩
      change F b = (a : V →L[ℂ] V) at hb
      change F b η = (a : V →L[ℂ] V) η
      exact congrArg (fun A : V →L[ℂ] V => A η) hb
    · rintro ⟨a, rfl⟩
      exact ⟨(⟨F a, ⟨a, rfl⟩⟩ : Q), rfl⟩
  change d T η ∈
    (Submodule.span ℂ (Set.range fun a : Q => (a : V →L[ℂ] V) η)).topologicalClosure at hOrbit
  rw [hOrbitRange, Submodule.span_eq] at hOrbit
  have hliteral (a : S) : Φ a =
      (WithLp.toLp 2 (fun i : Fin n => (a : H →L[ℂ] H) (ξ i)) : V) := by
    apply PiLp.ext
    intro i
    change d (a : H →L[ℂ] H) η i = (a : H →L[ℂ] H) (ξ i)
    exact finiteCoordinateStarAlgHom_apply (H := H) n (a : H →L[ℂ] H) η i
  have hLiteralRange : (LinearMap.range Φ : Set V) = Set.range (fun a : S =>
      (WithLp.toLp 2 (fun i : Fin n => (a : H →L[ℂ] H) (ξ i)) : V)) := by
    ext v
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (hliteral a).symm.trans ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (hliteral a).trans ha⟩
  have hTliteral : d T η = (WithLp.toLp 2 (fun i : Fin n => T (ξ i)) : V) := by
    apply PiLp.ext
    intro i
    exact finiteCoordinateStarAlgHom_apply (H := H) n T η i
  change d T η ∈ closure (LinearMap.range Φ : Set V) at hOrbit
  rw [hLiteralRange, hTliteral] at hOrbit
  exact hOrbit

end

end MathlibExt.Analysis.CStarAlgebra
