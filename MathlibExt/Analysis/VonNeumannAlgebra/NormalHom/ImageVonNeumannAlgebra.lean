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
# Von Neumann image of an injective normal homomorphism

For an injective normal unital complex star homomorphism `f : M → N`, its operator range
`R={f(x) : x ∈ M} ⊆ B(K)` is a von Neumann algebra on the target Hilbert space. The carrier is
exactly `R`, with the inherited operations and norm.

Its double-commutant equality is the range theorem for `f`; the construction does not enlarge
the carrier to a different generated algebra.
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

/-- **Concrete von Neumann algebra of an injective normal image.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. `imageVonNeumannAlgebra f` is the von
Neumann algebra on `K` with carrier `R` and inherited operator operations, satisfying
`R=R''`. -/
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

/-- **Operator carrier of the normal image algebra.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. the set underlying
`imageVonNeumannAlgebra f` is exactly `R={ (f(x) : B(K)) : x ∈ M }`. -/
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
