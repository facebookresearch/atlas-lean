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

public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Order.OrderClosed

/-!
# Spectral order and compact norm balls in ultraweak topology

For a concrete von Neumann algebra `M ⊆ B(H)` on a complete complex Hilbert space, its ultraweak
topology is `σ(M,M_*)`. Its spectral order is the operator order: `a≤b` when `b-a` is positive.

The relation `{(a,b) : a≤b}` is closed in the ultraweak product topology. For every real `r`,
the set `{x ∈ M : ‖x‖≤r}` is ultraweakly compact; negative radii give the empty set. The norm is
the inherited operator norm, and no supremum element is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Operator spectral order in the ultraweak algebra.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. `ultraweakPartialOrder M` is the order `a≤b` exactly when the bounded operator `b-a`
is positive, with algebra elements regarded in the ultraweak topology. -/
@[instance_reducible]
def ultraweakPartialOrder (M : VonNeumannAlgebra H) : PartialOrder (Ultraweak M) :=
  @PartialOrder.lift (Ultraweak M) M (CStarAlgebra.spectralOrder M)
    (ultraweakLinearEquiv M) (ultraweakLinearEquiv M).injective

/-- **Order comparison agrees across the ultraweak and normed algebras.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. two elements satisfy `a≤b` in the ultraweak algebra
exactly when their corresponding elements of `M` satisfy the spectral order relation. -/
theorem ultraweak_le_iff (M : VonNeumannAlgebra H) (a b : Ultraweak M) :
    @LE.le (Ultraweak M) (ultraweakPartialOrder M).toLE a b ↔
      @LE.le M (CStarAlgebra.spectralOrder M).toLE
        (ultraweakLinearEquiv M a) (ultraweakLinearEquiv M b) :=
  Iff.rfl

/-- **Ultraweak closedness of the spectral order relation.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. the set `{(a,b) ∈ M×M : a≤b}` is closed for the product of the ultraweak topologies. -/
theorem ultraweakOrderClosedTopology (M : VonNeumannAlgebra H) :
    @OrderClosedTopology (Ultraweak M) inferInstance (ultraweakPartialOrder M).toPreorder := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : PartialOrder (Ultraweak M) := ultraweakPartialOrder M
  let ι : M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype
  have horder (a b : M) : @LE.le M (CStarAlgebra.spectralOrder M).toLE a b ↔
      ((b - a : M) : H →L[ℂ] H).IsPositive := by
    have hembed : (a : H →L[ℂ] H) ≤ (b : H →L[ℂ] H) ↔
        @LE.le M (CStarAlgebra.spectralOrder M).toLE a b :=
      NonUnitalStarAlgHom.map_le_map_iff (A := M) (B := H →L[ℂ] H) ι Subtype.val_injective
    have hpositive : (a : H →L[ℂ] H) ≤ (b : H →L[ℂ] H) ↔
        ((b - a : M) : H →L[ℂ] H).IsPositive := by
      rw [ContinuousLinearMap.le_def]
      rfl
    exact hembed.symm.trans hpositive
  let f (ξ : H) (p : Ultraweak M × Ultraweak M) : ℂ :=
    star (vectorFunctional M ξ ξ (ultraweakLinearEquiv M p.2 - ultraweakLinearEquiv M p.1))
  have hcontinuous (ξ : H) : Continuous (f ξ) := by
    let ψ : normalFunctionalSpace M :=
      ⟨vectorFunctional M ξ ξ, vectorFunctional_mem_normalFunctionalSpace M ξ ξ⟩
    have hleft := (ultraweak_eval_continuous M ψ).comp
      (continuous_fst : Continuous fun p : Ultraweak M × Ultraweak M => p.1)
    have hright := (ultraweak_eval_continuous M ψ).comp
      (continuous_snd : Continuous fun p : Ultraweak M × Ultraweak M => p.2)
    have h := (hright.sub hleft).star
    convert h using 1
    funext p
    simp only [f, ψ, Pi.star_apply, Pi.sub_apply, Function.comp_def, map_sub]
  let t : Set (Ultraweak M × Ultraweak M) :=
    ⋂ ξ : H, {p | Complex.ofReal (f ξ p).re = f ξ p ∧ 0 ≤ (f ξ p).re}
  have hreal (ξ : H) : Continuous (fun p : Ultraweak M × Ultraweak M => (f ξ p).re) :=
    Complex.continuous_re.comp (hcontinuous ξ)
  have hclosed : IsClosed t := by
    apply isClosed_iInter
    intro ξ
    exact (isClosed_eq (Complex.continuous_ofReal.comp (hreal ξ)) (hcontinuous ξ)).inter
      (isClosed_le continuous_const (hreal ξ))
  have hset : {p : Ultraweak M × Ultraweak M |
      @LE.le (Ultraweak M) (ultraweakPartialOrder M).toLE p.1 p.2} = t := by
    ext p
    simp only [t, Set.mem_iInter, Set.mem_ofPred_eq]
    change @LE.le M (CStarAlgebra.spectralOrder M).toLE
      (ultraweakLinearEquiv M p.1) (ultraweakLinearEquiv M p.2) ↔
      ∀ ξ : H, Complex.ofReal (f ξ p).re = f ξ p ∧ 0 ≤ (f ξ p).re
    rw [horder, ContinuousLinearMap.isPositive_iff_complex]
    apply forall_congr'
    intro ξ
    have hvalue : f ξ p =
        ⟪((ultraweakLinearEquiv M p.2 - ultraweakLinearEquiv M p.1 : M) : H →L[ℂ] H) ξ, ξ⟫_ℂ := by
      dsimp only [f]
      rw [vectorFunctional_apply]
      exact inner_conj_symm _ _
    simp only [hvalue, RCLike.re_eq_complex_re]
  exact { isClosed_le' := hset.symm ▸ hclosed }

/-- **Ultraweak compactness of inherited operator-norm balls.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for every `r : ℝ`, `{x ∈ M : ‖x‖≤r}` is compact in the ultraweak topology; no
nonnegativity of `r` is required. -/
theorem ultraweakClosedBall_isCompact (M : VonNeumannAlgebra H) (r : ℝ) :
    IsCompact {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r} := by
  let e := ultraweakWeakDualHomeomorph M
  let s : Set (WeakDual ℂ (normalFunctionalSpace M)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (normalFunctionalSpace M)) r
  have hs : IsCompact s := WeakDual.isCompact_closedBall 0 r
  have hset : {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r} = e ⁻¹' s := by
    ext x
    change ‖ultraweakLinearEquiv M x‖ ≤ r ↔
      dist ((e x).toStrongDual) (0 : StrongDual ℂ (normalFunctionalSpace M)) ≤ r
    rw [dist_zero_right]
    change ‖ultraweakLinearEquiv M x‖ ≤ r ↔
      ‖normalFunctionalEvaluationEquiv M (ultraweakLinearEquiv M x)‖ ≤ r
    rw [(normalFunctionalEvaluationEquiv M).norm_map]
  rw [hset]
  exact e.isCompact_preimage.mpr hs

end

end VonNeumannAlgebra
