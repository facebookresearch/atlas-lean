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

public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Outer
public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin
public import MathlibExt.Analysis.Normed.Operator.Compact.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Bounded operators as multipliers of their actual compact ideal

Every double centralizer of the compact operators on a complete complex
Hilbert space is induced by an actual bounded operator. The forward map
is the existing universal multiplier extension, not a new constructor.
The compact coefficient structure is activated only locally, using its
existing inherited C-star structure. Zero Hilbert space is included.
-/

@[expose] public section

noncomputable section

open scoped CStarAlgebra MultiplierAlgebra

namespace DoubleCentralizer

universe uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The existing rank-one operator is genuinely in the compact ideal. -/
private theorem rankOne_mem_compact_ideal (x y : H) :
    InnerProductSpace.rankOne ℂ x y ∈
      (compactEndomorphismClosedStarIdeal (H := H)).carrier := by
  change IsCompactOperator (InnerProductSpace.rankOne ℂ x y)
  have hfinite : (ContinuousLinearMap.toSpanSingleton ℂ x).toLinearMap.HasFiniteRange :=
    LinearMap.HasFiniteRange.of_finite_dom
  have hcomp := hfinite.comp_right (innerSL ℂ y).toLinearMap
  have hrank : (InnerProductSpace.rankOne ℂ x y).toLinearMap.HasFiniteRange := by
    simpa only [InnerProductSpace.rankOne_def',
      ContinuousLinearMap.toLinearMap_comp] using hcomp
  exact hrank.isCompactOperator

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

The compact ideal has zero left annihilator, including zero Hilbert space. -/
theorem _root_.compactEndomorphismClosedStarIdeal_isEssential :
    (compactEndomorphismClosedStarIdeal (H := H)).IsEssential := by
  intro T hT
  apply ContinuousLinearMap.ext
  intro x
  suffices hxzero : T x = 0 by simpa only [zero_apply] using hxzero
  by_cases hx : x = 0
  · subst x
    exact map_zero T
  · have h := hT
      (⟨InnerProductSpace.rankOne ℂ x x, rankOne_mem_compact_ideal x x⟩ :
        (compactEndomorphismClosedStarIdeal (H := H)).carrier)
    have happly := congrArg (fun V : H →L[ℂ] H => V x) h
    change T (InnerProductSpace.rankOne ℂ x x x) = (0 : H →L[ℂ] H) x at happly
    simp only [InnerProductSpace.rankOne_apply, map_smul, zero_apply] at happly
    have hinner : inner ℂ x x ≠ 0 := inner_self_ne_zero.mpr hx
    exact (smul_eq_zero.mp happly).resolve_left hinner

/-- Normalize a nonzero vector using the existing complex scalar action. -/
private theorem exists_norm_one_vector
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [Nontrivial V] :
    ∃ e : V, ‖e‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  refine ⟨((‖x‖ : ℂ)⁻¹) • x, ?_⟩
  rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnorm]

/-- A unit vector recovers an actual bounded operator and both ordered actions. -/
private theorem exists_operator_with_actions_of_norm_one (e : H) (he : ‖e‖ = 1) :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let K := J.carrier;
    let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra;
    ∀ m : DoubleCentralizer ℂ K, ∃ T : H →L[ℂ] H,
      (∀ a : K, (m.fst a : H →L[ℂ] H) = T * (a : H →L[ℂ] H)) ∧
        ∀ a : K, (m.snd a : H →L[ℂ] H) = (a : H →L[ℂ] H) * T := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let K := J.carrier
  let EndH := H →L[ℂ] H
  let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra
  change ∀ m : DoubleCentralizer ℂ K, ∃ T : EndH,
    (∀ a : K, (m.fst a : EndH) = T * (a : EndH)) ∧
      ∀ a : K, (m.snd a : EndH) = (a : EndH) * T
  intro m
  let θ (x : H) : K :=
    ⟨InnerProductSpace.rankOne ℂ x e, rankOne_mem_compact_ideal x e⟩
  have hθadd (x y : H) : θ (x + y) = θ x + θ y := by
    apply Subtype.ext
    change InnerProductSpace.rankOne ℂ (x + y) e =
      InnerProductSpace.rankOne ℂ x e + InnerProductSpace.rankOne ℂ y e
    exact congrArg (fun f : H →L⋆[ℂ] EndH => f e)
      (map_add (InnerProductSpace.rankOne ℂ) x y)
  have hθsmul (z : ℂ) (x : H) : θ (z • x) = z • θ x := by
    apply Subtype.ext
    change InnerProductSpace.rankOne ℂ (z • x) e =
      z • InnerProductSpace.rankOne ℂ x e
    exact congrArg (fun f : H →L⋆[ℂ] EndH => f e)
      (map_smul (InnerProductSpace.rankOne ℂ) z x)
  have hθnorm (x : H) : ‖θ x‖ = ‖x‖ := by
    change ‖InnerProductSpace.rankOne ℂ x e‖ = ‖x‖
    rw [InnerProductSpace.norm_rankOne, he, mul_one]
  have heInner : inner ℂ e e = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, he]
  let f : H →ₗ[ℂ] H :=
    { toFun := fun x => (m.fst (θ x) : EndH) e
      map_add' := fun x y => by
        rw [hθadd]
        exact congrArg (fun a : K => (a : EndH) e) (map_add m.fst (θ x) (θ y))
      map_smul' := fun z x => by
        change (m.fst (θ (z • x)) : EndH) e = z • (m.fst (θ x) : EndH) e
        rw [hθsmul]
        exact congrArg (fun a : K => (a : EndH) e) (map_smul m.fst z (θ x)) }
  have hbound (x : H) : ‖f x‖ ≤ ‖m.fst‖ * ‖x‖ := by
    have hm := m.fst.le_opNorm (θ x)
    change ‖(m.fst (θ x) : EndH)‖ ≤ ‖m.fst‖ * ‖θ x‖ at hm
    calc
      ‖f x‖ ≤ ‖(m.fst (θ x) : EndH)‖ * ‖e‖ :=
        (m.fst (θ x) : EndH).le_opNorm e
      _ ≤ (‖m.fst‖ * ‖θ x‖) * ‖e‖ :=
        mul_le_mul_of_nonneg_right hm (norm_nonneg e)
      _ = ‖m.fst‖ * ‖x‖ := by rw [he, hθnorm, mul_one]
  let T : EndH := f.mkContinuous ‖m.fst‖ hbound
  have hT (x : H) : T x = (m.fst (θ x) : EndH) e := rfl
  have hLmul (a b : K) : m.fst (a * b) = m.fst a * b := by
    have h := congrArg (fun n : DoubleCentralizer ℂ K => n.fst b) (mul_coe m a)
    change m.fst (a * b) = m.fst a * b at h
    exact h
  refine ⟨T, ?_, ?_⟩
  · intro a
    apply ContinuousLinearMap.ext
    intro x
    have hθcomp : θ ((a : EndH) x) = a * θ x := by
      apply Subtype.ext
      change InnerProductSpace.rankOne ℂ ((a : EndH) x) e =
        (a : EndH) * InnerProductSpace.rankOne ℂ x e
      exact (InnerProductSpace.comp_rankOne x e (a : EndH)).symm
    change (m.fst a : EndH) x = T ((a : EndH) x)
    symm
    rw [hT, hθcomp, hLmul]
    change (m.fst a : EndH) (InnerProductSpace.rankOne ℂ x e e) =
      (m.fst a : EndH) x
    rw [InnerProductSpace.rankOne_apply, heInner, one_smul]
  · intro a
    apply ContinuousLinearMap.ext
    intro x
    have hrank : InnerProductSpace.rankOne ℂ x e e = x := by
      rw [InnerProductSpace.rankOne_apply, heInner, one_smul]
    have h := congrArg (fun b : K => (b : EndH) e) (m.central a (θ x))
    change (m.snd a : EndH) (InnerProductSpace.rankOne ℂ x e e) =
      (a : EndH) ((m.fst (θ x) : EndH) e) at h
    change (m.snd a : EndH) x = (a : EndH) (T x)
    calc
      _ = (m.snd a : EndH) (InnerProductSpace.rankOne ℂ x e e) :=
        congrArg (fun y : H => (m.snd a : EndH) y) hrank.symm
      _ = (a : EndH) ((m.fst (θ x) : EndH) e) := h
      _ = (a : EndH) (T x) :=
        congrArg (fun y : H => (a : EndH) y) (hT x).symm

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

Every multiplier of the compact ideal is induced by a bounded operator. No unit vector,
nontriviality or desired action law is a caller hypothesis. -/
theorem multiplierExtensionUnital_compact_surjective :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    Function.Surjective
      (multiplierExtensionUnital J (StarAlgEquiv.refl ℂ J.carrier)) := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let K := J.carrier
  let EndH := H →L[ℂ] H
  let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra
  classical
  change Function.Surjective
    (multiplierExtensionUnital J (StarAlgEquiv.refl ℂ K))
  intro m
  rcases subsingleton_or_nontrivial H with hzero | hnonzero
  · let _ : Subsingleton H := hzero
    refine ⟨0, ?_⟩
    apply DoubleCentralizer.ext ℂ K
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
    · apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      exact Subsingleton.elim _ _
    · apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      exact Subsingleton.elim _ _
  · let _ : Nontrivial H := hnonzero
    obtain ⟨e, he⟩ := exists_norm_one_vector H
    obtain ⟨T, hleft, hright⟩ :=
      exists_operator_with_actions_of_norm_one e he m
    refine ⟨T, ?_⟩
    apply DoubleCentralizer.ext ℂ K
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro a
      apply Subtype.ext
      have h := multiplierExtension_fst J (StarAlgEquiv.refl ℂ K) T a
      change ((multiplierExtension J (StarAlgEquiv.refl ℂ K) T).fst a : EndH) =
        (m.fst a : EndH)
      change ((multiplierExtension J (StarAlgEquiv.refl ℂ K) T).fst a : EndH) =
        T * (a : EndH) at h
      exact h.trans (hleft a).symm
    · apply ContinuousLinearMap.ext
      intro a
      apply Subtype.ext
      have h := multiplierExtension_snd J (StarAlgEquiv.refl ℂ K) T a
      change ((multiplierExtension J (StarAlgEquiv.refl ℂ K) T).snd a : EndH) =
        (m.snd a : EndH)
      change ((multiplierExtension J (StarAlgEquiv.refl ℂ K) T).snd a : EndH) =
        (a : EndH) * T at h
      exact h.trans (hright a).symm

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

The bounded-operator algebra is star-algebra equivalent to the multipliers of its compact ideal,
on the existing universal map. -/
noncomputable def compactMultiplierEquiv :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    (H →L[ℂ] H) ≃⋆ₐ[ℂ] DoubleCentralizer ℂ J.carrier := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let K := J.carrier
  let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra
  refine StarAlgEquiv.ofBijective
    (multiplierExtensionUnital J (StarAlgEquiv.refl ℂ K))
    ⟨?_, multiplierExtensionUnital_compact_surjective (H := H)⟩
  change Function.Injective (multiplierExtension J (StarAlgEquiv.refl ℂ K))
  exact multiplierExtension_injective J (StarAlgEquiv.refl ℂ K)
    (compactEndomorphismClosedStarIdeal_isEssential (H := H))

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

The forward equivalence is literally the existing multiplier extension. -/
@[simp]
theorem compactMultiplierEquiv_apply (T : H →L[ℂ] H) :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    compactMultiplierEquiv (H := H) T =
      multiplierExtensionUnital J (StarAlgEquiv.refl ℂ J.carrier) T := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra
  rfl

end DoubleCentralizer
