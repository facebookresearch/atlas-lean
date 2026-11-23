/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Idele

/-!
# Discreteness of principal ideles

ATLAS NumberTheoryI N543 / Proposition 26.6, in the native restricted-product
model: the principal ideles embed discretely.
-/

@[expose] public section

noncomputable section

namespace NumberField.TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- If the finite principal idele of `x` lies in the all-integral-unit locus,
i.e. the range of `RestrictedProduct.structureMap`, then `x` is an algebraic
integer. -/
private theorem exists_mem_ringOfIntegers_of_mem_range (x : Kˣ)
    (hx : finitePrincipalEmbedding (𝓞 K) K x ∈ Set.range
      (RestrictedProduct.structureMap
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          (v.adicCompletion K)ˣ)
        (fun v => (localIntegralUnitSubgroup (𝓞 K) K v : Set _))
        Filter.cofinite)) :
    ∃ k : 𝓞 K, algebraMap (𝓞 K) K k = (x : K) := by
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K (x : K)
  intro v
  obtain ⟨y, hy⟩ := hx
  have hcoord : ∀ w,
      (RestrictedProduct.structureMap
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          (v.adicCompletion K)ˣ)
        (fun v => (localIntegralUnitSubgroup (𝓞 K) K v : Set _))
        Filter.cofinite) y w = finitePrincipalEmbedding (𝓞 K) K x w :=
    fun w => congrFun (congrArg DFunLike.coe hy) w
  have hmem : finitePrincipalEmbedding (𝓞 K) K x v ∈
      (localIntegralUnitSubgroup (𝓞 K) K v : Set _) := by
    rw [← hcoord v]
    exact (y v).2
  rw [finitePrincipalEmbedding_apply] at hmem
  have hintegral := ((mem_localIntegralUnitSubgroup (𝓞 K) K).mp hmem).1
  change Valued.v
      (((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1 at hintegral
  have hunit :
      (((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) (x : K) := rfl
  rw [hunit] at hintegral
  have hcoerce : algebraMap K (v.adicCompletion K) (x : K)
      = ((x : K) : v.adicCompletion K) := by
    rw [congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
      (𝓞 K) K v) (x : K)]
    simp
  rw [hcoerce, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    (x : K)] at hintegral
  exact hintegral

private theorem eq_one_of_forall_infinitePlace_norm_sub_one_lt_one
    (k : 𝓞 K)
    (h : ∀ w : InfinitePlace K,
      ‖algebraMap K w.Completion (k : K) - 1‖ < 1) :
    k = 1 := by
  have hall : ∀ w : InfinitePlace K, w (((k - 1 : 𝓞 K) : K)) < 1 := by
    intro w
    have hw := h w
    rw [← map_one (algebraMap K w.Completion), ← map_sub] at hw
    have hco : algebraMap K w.Completion ((k : K) - 1) =
        (↑((WithAbs.equiv w.1).symm ((k : K) - 1)) : w.Completion) := rfl
    rw [hco, NumberField.InfinitePlace.Completion.norm_coe] at hw
    simpa using hw
  have hk0 : k - 1 = 0 := by
    by_contra hk
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hge : 1 ≤ w₀ (((k - 1 : 𝓞 K) : K)) :=
      NumberField.InfinitePlace.one_le_of_lt_one hk (fun {_} _ => hall _)
    exact (not_lt_of_ge hge) (hall w₀)
  exact sub_eq_zero.mp hk0

/-- **The principal ideles are discrete.** For a number field $K$, the subgroup of principal
ideles is discrete in the idele group of $K$, where the idele group carries the product of the
product topology at the infinite places and the restricted-product topology at the finite
places. -/
public theorem principalIdeles_discrete :
    DiscreteTopology (principalIdeles (𝓞 K) K) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  rw [isOpen_induced_iff]
  classical
  set UInf : Set (InfiniteIdeleGroup K) :=
    {a | ∀ w : InfinitePlace K, ‖(a w : w.Completion) - 1‖ < 1} with hUInf
  set UFin : Set (FiniteIdeleGroup (𝓞 K) K) := Set.range
    (RestrictedProduct.structureMap
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (v.adicCompletion K)ˣ)
      (fun v => (localIntegralUnitSubgroup (𝓞 K) K v : Set _))
      Filter.cofinite) with hUFin
  set U : Set (TopologicalIdeleGroup (𝓞 K) K) := UInf ×ˢ UFin with hU
  refine ⟨U, ?_, ?_⟩
  · have hInf : IsOpen UInf := by
      have : UInf = ⋂ w : InfinitePlace K,
          {a | ‖(a w : w.Completion) - 1‖ < 1} := by
        ext a
        simp [hUInf]
      rw [this]
      exact isOpen_iInter_of_finite fun w => isOpen_lt
        (continuous_norm.comp
          ((Units.continuous_val.comp (continuous_apply w)).sub continuous_const))
        continuous_const
    have hFin : IsOpen UFin := by
      rw [hUFin]
      exact (RestrictedProduct.isOpenEmbedding_structureMap
        (fun v => FiniteIdeleGroup.isOpen_localIntegralUnitSubgroup
          (𝓞 K) K v)).isOpen_range
    exact hInf.prod hFin
  · ext a
    change
      (((a : TopologicalIdeleGroup (𝓞 K) K).1 ∈ UInf ∧
        (a : TopologicalIdeleGroup (𝓞 K) K).2 ∈ UFin) ↔ a = 1)
    constructor
    · rintro ⟨hInf, hFin⟩
      obtain ⟨x, hx⟩ := a.property
      have hsnd : finitePrincipalEmbedding (𝓞 K) K x =
          (a : TopologicalIdeleGroup (𝓞 K) K).2 := by
        rw [← principalEmbedding_snd (𝓞 K) K x]
        exact congrArg (fun z : TopologicalIdeleGroup (𝓞 K) K => z.2) hx
      have hfst : infinitePrincipalEmbedding K x =
          (a : TopologicalIdeleGroup (𝓞 K) K).1 := by
        rw [← principalEmbedding_fst (𝓞 K) K x]
        exact congrArg (fun z : TopologicalIdeleGroup (𝓞 K) K => z.1) hx
      have hfinmem : finitePrincipalEmbedding (𝓞 K) K x ∈ UFin := by
        rw [hsnd]
        exact hFin
      obtain ⟨k, hk⟩ := exists_mem_ringOfIntegers_of_mem_range K x hfinmem
      have hnorm : ∀ w : InfinitePlace K,
          ‖algebraMap K w.Completion (k : K) - 1‖ < 1 := by
        intro w
        have hw := hInf w
        rw [← hfst, infinitePrincipalEmbedding_apply,
          Units.coe_map] at hw
        have hkk : (x : K) = (k : K) := hk.symm
        rw [hkk] at hw
        exact hw
      have hk1 : k = 1 := eq_one_of_forall_infinitePlace_norm_sub_one_lt_one K k hnorm
      have hx1 : x = 1 := by
        apply Units.ext
        have : algebraMap (𝓞 K) K k = algebraMap (𝓞 K) K 1 := by rw [hk1]
        simpa [hk] using this
      have : (a : TopologicalIdeleGroup (𝓞 K) K) = 1 := by
        rw [← hx, hx1]
        rfl
      exact Subtype.ext this
    · intro ha
      have ha1 : (a : TopologicalIdeleGroup (𝓞 K) K) = 1 := congrArg Subtype.val ha
      refine ⟨?_, ?_⟩
      · intro w
        rw [ha1]
        change ‖((1 : (w.Completion)ˣ) : w.Completion) - 1‖ < 1
        simp
      · rw [ha1]
        change (1 : FiniteIdeleGroup (𝓞 K) K) ∈ UFin
        rw [hUFin]
        refine ⟨fun v => (1 : localIntegralUnitSubgroup (𝓞 K) K v), ?_⟩
        apply DFunLike.coe_injective
        funext v
        rfl

end NumberField.TopologicalIdeleGroup
