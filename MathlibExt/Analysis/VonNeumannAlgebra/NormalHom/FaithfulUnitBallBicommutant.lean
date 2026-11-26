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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulWOTBall
public import MathlibExt.Analysis.CStarAlgebra.BicommutantStrongClosureEquality
public import MathlibExt.Analysis.CStarAlgebra.KaplanskyDensity

/-!
# Unit ball of the bicommutant lies in the normal operator image

Let `f : M → N` be an injective normal unital complex star homomorphism and `R ⊆ B(K)` its
operator range. If `T ∈ R''` and `‖T‖≤1`, then `T ∈ R`.

The statement provides an operator-image conclusion from bicommutant membership and a unit-ball
bound. No preimage or closed range is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Topology

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- **Bounded bicommutant operator belongs to the injective normal image.** Let `M,N` be
concrete von Neumann algebras on complete complex Hilbert spaces. Their normal-functional
Banach spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their
ultraweak topologies are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star
homomorphism that is ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) :
B(K)) : x ∈ M }` for its operator range on the target Hilbert space `K`. if `T ∈ B(K)`
commutes with every operator in the commutant `R'` and `‖T‖≤1`, then `T∈R`, equivalently
there is `x ∈ M` with `(f(x) : B(K))=T`. -/
theorem unitBall_bicommutant_mem_operatorRange (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (T : K →L[ℂ] K)
    (hT : T ∈ Set.centralizer (Set.centralizer
      (Set.range fun x : M => (f x : K →L[ℂ] K)))) (hTnorm : ‖T‖ ≤ 1) :
    T ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) := by
  classical
  let g : M →⋆ₐ[ℂ] (K →L[ℂ] K) := N.toStarSubalgebra.subtype.comp f.toStarAlgHom
  let S := g.range
  have hRange : (S : Set (K →L[ℂ] K)) = Set.range (fun x : M => (f x : K →L[ℂ] K)) := by
    ext A
    constructor
    · rintro ⟨x, hx⟩
      change (f x : K →L[ℂ] K) = A at hx
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change (f x : K →L[ℂ] K) = A
      exact hx
  let P := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) K {s : Set K | Finite s}
  let W : (K →Lₚₜ[ℂ] K) → (K →WOT[ℂ] K) := fun p => ContinuousLinearMapWOT.ofCLM (P.symm p)
  have hPvalue (p : K →Lₚₜ[ℂ] K) (ξ : K) : P.symm p ξ = p ξ :=
    ContinuousLinearMap.toUniformConvergenceCLM_symm_apply
  have hWvalue (p : K →Lₚₜ[ℂ] K) : (W p).toCLM = P.symm p :=
    ContinuousLinearMapWOT.toCLM_ofCLM _
  have hW : Continuous W := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro ξ φ
    have h := φ.continuous.comp
      (continuous_eval_const ξ : Continuous (fun p : K →Lₚₜ[ℂ] K => p ξ))
    simpa only [Function.comp_def, W, ContinuousLinearMapWOT.ofCLM_apply, hPvalue] using h
  have hSource : Set.range (fun a : S => P (a : K →L[ℂ] K)) =
      {p : K →Lₚₜ[ℂ] K | P.symm p ∈ S} := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      change P.symm (P (a : K →L[ℂ] K)) ∈ S
      rw [P.symm_apply_apply]
      exact a.property
    · intro hp
      change P.symm p ∈ S at hp
      refine ⟨⟨P.symm p, hp⟩, ?_⟩
      exact P.apply_symm_apply p
  have hTS : T ∈ Set.centralizer (Set.centralizer (S : Set (K →L[ℂ] K))) := by
    rw [hRange]
    exact hT
  have hStrong := MathlibExt.Analysis.CStarAlgebra.bicommutant_mem_strongClosure S T hTS
  rw [hSource] at hStrong
  let B : Set (K →Lₚₜ[ℂ] K) := {p | P.symm p ∈ S ∧ ‖P.symm p‖ ≤ 1}
  have hKaplansky : closure B =
      {p : K →Lₚₜ[ℂ] K | p ∈ closure {q : K →Lₚₜ[ℂ] K | P.symm q ∈ S} ∧ ‖P.symm p‖ ≤ 1} :=
    MathlibExt.Analysis.CStarAlgebra.KaplanskyDensityWanted.kaplansky_density_theorem S
  have hBall : P T ∈ closure B := by
    rw [hKaplansky]
    refine ⟨hStrong, ?_⟩
    rw [P.symm_apply_apply]
    exact hTnorm
  let C : Set (K →WOT[ℂ] K) := {q |
    q.toCLM ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) ∧ ‖q.toCLM‖ ≤ 1}
  have hMaps : Set.MapsTo W B C := by
    intro p hp
    change P.symm p ∈ S ∧ ‖P.symm p‖ ≤ 1 at hp
    change (W p).toCLM ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) ∧ ‖(W p).toCLM‖ ≤ 1
    rw [hWvalue]
    refine ⟨?_, hp.2⟩
    rw [← hRange]
    exact hp.1
  have hClosed : IsClosed C := f.isClosed_wot_range_inter_ball hf 1
  have hImage : W (P T) ∈ closure C := map_mem_closure hW hBall hMaps
  rw [hClosed.closure_eq] at hImage
  change (W (P T)).toCLM ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) ∧
    ‖(W (P T)).toCLM‖ ≤ 1 at hImage
  rw [hWvalue, P.symm_apply_apply] at hImage
  exact hImage.1

end

end VonNeumannAlgebra.NormalStarAlgHom
