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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulBicommutantRange

/-!
# The actual von Neumann image of a faithful normal homomorphism

The carrier is the literal original operator range star subalgebra. The
proved full double-commutant equality supplies exactly its required
von Neumann closure field. Every image element is an original map value;
no generated larger carrier, desired image or closure certificate is input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The literal faithful normal operator image, with its proved von Neumann closure field. -/
def imageVonNeumannAlgebra (f : NormalStarAlgHom M N) (hf : Function.Injective f) : VonNeumannAlgebra K :=
  let g : M →⋆ₐ[ℂ] (K →L[ℂ] K) := N.toStarSubalgebra.subtype.comp f.toStarAlgHom
  { g.range with
    centralizer_centralizer' := by
      have hRange : (g.range : Set (K →L[ℂ] K)) =
          Set.range (fun x : M => (f x : K →L[ℂ] K)) := by
        ext T
        constructor
        · rintro ⟨x, hx⟩
          change (f x : K →L[ℂ] K) = T at hx
          exact ⟨x, hx⟩
        · rintro ⟨x, hx⟩
          refine ⟨x, ?_⟩
          change (f x : K →L[ℂ] K) = T
          exact hx
      change Set.centralizer (Set.centralizer (g.range : Set (K →L[ℂ] K))) =
        (g.range : Set (K →L[ℂ] K))
      rw [hRange]
      exact (f.operatorRange_eq_bicommutant hf).symm }

/-- The constructed von Neumann carrier is exactly the original concrete operator range. -/
theorem coe_imageVonNeumannAlgebra (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    (f.imageVonNeumannAlgebra hf : Set (K →L[ℂ] K)) =
      Set.range (fun x : M => (f x : K →L[ℂ] K)) := by
  change ((N.toStarSubalgebra.subtype.comp f.toStarAlgHom).range : Set (K →L[ℂ] K)) =
    Set.range (fun x : M => (f x : K →L[ℂ] K))
  ext T
  constructor
  · rintro ⟨x, hx⟩
    change (f x : K →L[ℂ] K) = T at hx
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change (f x : K →L[ℂ] K) = T
    exact hx

end

end VonNeumannAlgebra.NormalStarAlgHom
