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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.ImageHom
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.RangeHomeomorph
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalEquiv

/-!
# Normal equivalence onto an injective homomorphism's image

An injective normal unital complex star homomorphism `f : M → N` gives a normal star-algebra
equivalence `e : M ≃ R`, where `R={f(x) : x ∈ M}` is its concrete von Neumann image algebra.

The forward value is `e(x)=f(x)`, and its inverse returns the source element with the prescribed
image operator. Both directions are ultraweakly continuous.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- **Normal star equivalence onto the von Neumann image.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. `f.imageEquiv : NormalStarAlgEquiv M
R` is the star equivalence with forward map `x ↦ f(x)`, ultraweakly continuous in both
directions. -/
def imageEquiv (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    NormalStarAlgEquiv M (f.imageVonNeumannAlgebra hf) := by
  let P := f.imageVonNeumannAlgebra hf
  let q : NormalStarAlgHom M P := f.toImage hf
  have hqi : Function.Injective q := f.toImage_injective hf
  have hqs : Function.Surjective q := f.toImage_surjective hf
  let e : M ≃⋆ₐ[ℂ] P := StarAlgEquiv.ofBijective q.toStarAlgHom ⟨hqi, hqs⟩
  have he (a : M) : e a = q a := rfl
  let invU : Ultraweak P → Ultraweak M := fun y =>
    (ultraweakLinearEquiv M).symm (e.symm (ultraweakLinearEquiv P y))
  have hinvValue (y : Ultraweak P) : q.ultraweakMap (invU y) = y := by
    rw [q.ultraweakMap_apply]
    dsimp only [invU]
    rw [LinearEquiv.apply_symm_apply]
    change (ultraweakLinearEquiv P).symm (e (e.symm (ultraweakLinearEquiv P y))) = y
    rw [e.apply_symm_apply, LinearEquiv.symm_apply_apply]
  have hqUL : Function.Injective q.ultraweakMap := by
    intro x y h
    apply (ultraweakLinearEquiv M).injective
    apply hqi
    have hvalue := congrArg (ultraweakLinearEquiv P) h
    simpa only [q.ultraweakMap_apply, LinearEquiv.apply_symm_apply] using hvalue
  let rhome := q.ultraweakRangeHomeomorph hqi
  let j : Ultraweak P → Set.range q.ultraweakMap :=
    fun y => ⟨y, ⟨invU y, hinvValue y⟩⟩
  have hj : Continuous j := continuous_id.subtype_mk (fun y => ⟨invU y, hinvValue y⟩)
  have hinverse : Continuous invU := by
    have hcomp : Continuous (fun y : Ultraweak P => rhome.symm (j y)) := by
      simpa only [Function.comp_def] using rhome.symm.continuous.comp hj
    have hfun : (fun y : Ultraweak P => rhome.symm (j y)) = invU := by
      funext y
      apply hqUL
      have h := congrArg (fun z : Set.range q.ultraweakMap => z.val) (rhome.apply_symm_apply (j y))
      change (q.ultraweakRangeHomeomorph hqi (rhome.symm (j y))).val = y at h
      rw [q.ultraweakRangeHomeomorph_apply] at h
      calc
        q.ultraweakMap (rhome.symm (j y)) = y := h
        _ = q.ultraweakMap (invU y) := (hinvValue y).symm
    rw [hfun] at hcomp
    exact hcomp
  exact
    { toStarAlgEquiv := e
      continuous_ultraweak := by
        change Continuous (fun x : Ultraweak M =>
          (ultraweakLinearEquiv P).symm (q.toStarAlgHom (ultraweakLinearEquiv M x)))
        exact q.continuous_ultraweak
      continuous_ultraweak_symm := hinverse }

/-- **Forward operator value of the normal image equivalence.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. for `x ∈ M`, the operator underlying
`f.imageEquiv x` is `(f(x) : B(K))`. -/
@[simp]
theorem imageEquiv_apply (f : NormalStarAlgHom M N) (hf : Function.Injective f) (a : M) :
    (f.imageEquiv hf a : K →L[ℂ] K) = (f a : K →L[ℂ] K) := by
  have hb : Function.Bijective (f.toImage hf).toStarAlgHom := by
    change Function.Bijective (f.toImage hf)
    exact ⟨f.toImage_injective hf, f.toImage_surjective hf⟩
  have h := StarAlgEquiv.ofBijective_apply (f := (f.toImage hf).toStarAlgHom) hb a
  change ((StarAlgEquiv.ofBijective (f.toImage hf).toStarAlgHom hb) a : K →L[ℂ] K) =
    (f a : K →L[ℂ] K)
  exact (congrArg (fun b : f.imageVonNeumannAlgebra hf => (b : K →L[ℂ] K)) h).trans
    (f.toImage_apply hf a)

/-- **Source preimage of an image-algebra operator.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. for `y ∈ R`, the inverse `e⁻¹(y)` of
`e=f.imageEquiv` satisfies `(f(e⁻¹(y)) : B(K))=(y : B(K))`. -/
theorem imageEquiv_symm_operator_value (f : NormalStarAlgHom M N) (hf : Function.Injective f)
    (b : f.imageVonNeumannAlgebra hf) :
    (f ((f.imageEquiv hf).toStarAlgEquiv.symm b) : K →L[ℂ] K) = (b : K →L[ℂ] K) := by
  have h := (f.imageEquiv hf).toStarAlgEquiv.apply_symm_apply b
  have hvalue := congrArg (fun p : f.imageVonNeumannAlgebra hf => (p : K →L[ℂ] K)) h
  simpa only [NormalStarAlgEquiv.toStarAlgEquiv_apply, imageEquiv_apply] using hvalue

end

end VonNeumannAlgebra.NormalStarAlgHom
