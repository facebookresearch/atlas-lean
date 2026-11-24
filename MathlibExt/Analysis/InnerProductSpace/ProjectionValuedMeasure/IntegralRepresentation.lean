/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Integral

/-!
# The spectral-integral representation

Spectral integration sends bounded measurable functions to bounded operators as a unital complex
star-algebra homomorphism.  Multiplication and star preservation are first proved for measurable
simple functions by refining their measurable fibers, then extended through uniform simple-function
density and continuity.  No regularity, separability, or nonemptiness hypothesis is required.

## Primary source

John B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter IX, §1,
Proposition 1.12. The domain is bounded measurable functions on an arbitrary
measurable space. Reconstruction converses for continuous-function algebras,
including noncompact `C₀(X)`, are outside this module.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped InnerProductSpace Topology

open MathlibExt.MeasureTheory.Function

namespace MathlibExt.Analysis.InnerProductSpace
namespace ProjectionValuedMeasure

noncomputable section

universe u v

variable {X : Type u} {H : Type v}
variable [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem ofSimpleFunc_eq_sum_indicatorConst (f : SimpleFunc X ℂ) :
    BoundedMeasurableFunction.ofSimpleFunc f =
      ∑ c ∈ f.range, BoundedMeasurableFunction.indicatorConst
        (f ⁻¹' {c}) (f.measurableSet_fiber c) c := by
  classical
  apply Subtype.ext
  apply lp.ext
  funext x
  change BoundedMeasurableFunction.ofSimpleFunc f x =
    (∑ c ∈ f.range, BoundedMeasurableFunction.indicatorConst
      (f ⁻¹' {c}) (f.measurableSet_fiber c) c) x
  have hsum := congrArg (fun q : lp (fun _ : X ↦ ℂ) ⊤ ↦ q x)
    (map_sum (boundedMeasurableFunctions X).subtype
      (fun c ↦ BoundedMeasurableFunction.indicatorConst
        (f ⁻¹' {c}) (f.measurableSet_fiber c) c) f.range)
  have hsum_apply :
      (∑ c ∈ f.range, BoundedMeasurableFunction.indicatorConst
        (f ⁻¹' {c}) (f.measurableSet_fiber c) c) x =
      ∑ c ∈ f.range, (f ⁻¹' {c}).indicator (fun _ ↦ c) x := by
    simpa only [StarSubalgebra.subtype_apply, lp.coeFn_sum, Finset.sum_apply,
      BoundedMeasurableFunction.indicatorConst_apply] using hsum
  rw [BoundedMeasurableFunction.ofSimpleFunc_apply, hsum_apply]
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro c hc hcf
    simp [hcf.symm]
  · exact fun hnot ↦ (hnot (f.mem_range_self x)).elim

private theorem star_indicatorConst (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    star (BoundedMeasurableFunction.indicatorConst s hs c) =
      BoundedMeasurableFunction.indicatorConst s hs (star c) := by
  apply Subtype.ext
  apply lp.ext
  funext x
  change star (BoundedMeasurableFunction.indicatorConst s hs c x) = _
  by_cases hx : x ∈ s <;> simp [BoundedMeasurableFunction.indicatorConst_apply, hx]

private theorem indicatorConst_mul (s t : Set X) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (c d : ℂ) :
    BoundedMeasurableFunction.indicatorConst s hs c *
        BoundedMeasurableFunction.indicatorConst t ht d =
      BoundedMeasurableFunction.indicatorConst (s ∩ t) (hs.inter ht) (c * d) := by
  apply Subtype.ext
  apply lp.ext
  funext x
  change BoundedMeasurableFunction.indicatorConst s hs c x *
      BoundedMeasurableFunction.indicatorConst t ht d x = _
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
    simp [BoundedMeasurableFunction.indicatorConst_apply, hxs, hxt]

private theorem spectralIntegral_star_ofSimpleFunc
    (E : ProjectionValuedMeasure X H) (f : SimpleFunc X ℂ) :
    spectralIntegral E (star (BoundedMeasurableFunction.ofSimpleFunc f)) =
      star (spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc f)) := by
  classical
  calc
    spectralIntegral E (star (BoundedMeasurableFunction.ofSimpleFunc f)) =
        spectralIntegral E
          (∑ c ∈ f.range, BoundedMeasurableFunction.indicatorConst
            (f ⁻¹' {c}) (f.measurableSet_fiber c) (star c)) := by
      congr 1
      rw [ofSimpleFunc_eq_sum_indicatorConst, star_sum]
      apply Finset.sum_congr rfl
      intro c hc
      exact star_indicatorConst (f ⁻¹' {c}) (f.measurableSet_fiber c) c
    _ = ∑ c ∈ f.range, star c • E (f ⁻¹' {c}) := by
      rw [← spectralIntegralCLM_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [spectralIntegralCLM_apply, spectralIntegral_indicatorConst]
    _ = star (simpleSpectralIntegral E f) := by
      rw [simpleSpectralIntegral, star_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [star_smul, (E.isStarProjection (f ⁻¹' {c})).isSelfAdjoint.star_eq]
    _ = star (spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc f)) := by
      rw [spectralIntegral_ofSimpleFunc]

private theorem smul_projection_mul_smul_projection
    (E : ProjectionValuedMeasure X H) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (c d : ℂ) :
    (c • E s) * (d • E t) = (c * d) • E (s ∩ t) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← E.inter s hs t ht]

private theorem simpleSpectralIntegral_mul
    (E : ProjectionValuedMeasure X H) (f g : SimpleFunc X ℂ) :
    simpleSpectralIntegral E f * simpleSpectralIntegral E g =
      ∑ c ∈ f.range, ∑ d ∈ g.range,
        (c * d) • E ((f ⁻¹' {c}) ∩ (g ⁻¹' {d})) := by
  classical
  rw [simpleSpectralIntegral, simpleSpectralIntegral, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact smul_projection_mul_smul_projection E _ _
    (f.measurableSet_fiber c) (g.measurableSet_fiber d) c d

private theorem spectralIntegral_mul_ofSimpleFunc
    (E : ProjectionValuedMeasure X H) (f g : SimpleFunc X ℂ) :
    spectralIntegral E
        (BoundedMeasurableFunction.ofSimpleFunc f *
          BoundedMeasurableFunction.ofSimpleFunc g) =
      spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc f) *
        spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc g) := by
  classical
  calc
    spectralIntegral E
        (BoundedMeasurableFunction.ofSimpleFunc f *
          BoundedMeasurableFunction.ofSimpleFunc g) =
        spectralIntegral E
          (∑ c ∈ f.range, ∑ d ∈ g.range,
            BoundedMeasurableFunction.indicatorConst
              ((f ⁻¹' {c}) ∩ (g ⁻¹' {d}))
              ((f.measurableSet_fiber c).inter (g.measurableSet_fiber d)) (c * d)) := by
      congr 1
      rw [ofSimpleFunc_eq_sum_indicatorConst, ofSimpleFunc_eq_sum_indicatorConst,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      exact indicatorConst_mul _ _ (f.measurableSet_fiber c)
        (g.measurableSet_fiber d) c d
    _ = ∑ c ∈ f.range, ∑ d ∈ g.range,
        (c * d) • E ((f ⁻¹' {c}) ∩ (g ⁻¹' {d})) := by
      rw [← spectralIntegralCLM_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [spectralIntegralCLM_apply, spectralIntegral_indicatorConst]
    _ = simpleSpectralIntegral E f * simpleSpectralIntegral E g :=
      (simpleSpectralIntegral_mul E f g).symm
    _ = spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc f) *
        spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc g) := by
      rw [spectralIntegral_ofSimpleFunc, spectralIntegral_ofSimpleFunc]

private theorem denseRange_ofSimpleFunc :
    DenseRange (BoundedMeasurableFunction.ofSimpleFunc :
      SimpleFunc X ℂ → BoundedMeasurableFunction X) := by
  rw [Metric.denseRange_iff]
  intro phi epsilon hepsilon
  obtain ⟨f, hf⟩ := BoundedMeasurableFunction.exists_simpleFunc_norm_sub_lt phi hepsilon
  refine ⟨f, ?_⟩
  simpa [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hf

/-- Spectral integration preserves the pointwise star operation. -/
theorem spectralIntegral_star
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    spectralIntegral E (star phi) = star (spectralIntegral E phi) := by
  have hstar : Continuous (star : BoundedMeasurableFunction X →
      BoundedMeasurableFunction X) := by
    exact continuous_induced_rng.2
      (continuous_subtype_val : Continuous (Subtype.val :
        BoundedMeasurableFunction X → lp (fun _ : X ↦ ℂ) ⊤)).star
  have hEq :
      (fun psi : BoundedMeasurableFunction X ↦ spectralIntegral E (star psi)) =
        fun psi ↦ star (spectralIntegral E psi) := by
    apply denseRange_ofSimpleFunc (X := X) |>.equalizer
    · simpa only [Function.comp_def, spectralIntegralCLM_apply] using
        (spectralIntegralCLM E).continuous.comp hstar
    · simpa only [Function.comp_def, spectralIntegralCLM_apply] using
        continuous_star.comp (spectralIntegralCLM E).continuous
    · funext f
      exact spectralIntegral_star_ofSimpleFunc E f
  exact congrFun hEq phi

/-- Spectral integration preserves multiplication. -/
theorem spectralIntegral_mul
    (E : ProjectionValuedMeasure X H) (phi psi : BoundedMeasurableFunction X) :
    spectralIntegral E (phi * psi) = spectralIntegral E phi * spectralIntegral E psi := by
  have hright (g : SimpleFunc X ℂ) :
      ∀ theta : BoundedMeasurableFunction X,
        spectralIntegral E (theta * BoundedMeasurableFunction.ofSimpleFunc g) =
          spectralIntegral E theta *
            spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc g) := by
    have hEq :
        (fun theta : BoundedMeasurableFunction X ↦
          spectralIntegral E (theta * BoundedMeasurableFunction.ofSimpleFunc g)) =
          fun theta ↦ spectralIntegral E theta *
            spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc g) := by
      apply denseRange_ofSimpleFunc (X := X) |>.equalizer
      · have hm : Continuous (fun theta : BoundedMeasurableFunction X ↦
            theta * BoundedMeasurableFunction.ofSimpleFunc g) := by
          exact continuous_id'.mul_const (BoundedMeasurableFunction.ofSimpleFunc g)
        simpa only [Function.comp_def, spectralIntegralCLM_apply] using
          (spectralIntegralCLM E).continuous.comp hm
      · simpa only [spectralIntegralCLM_apply] using
          (spectralIntegralCLM E).continuous.mul_const
            (spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc g))
      · funext f
        exact spectralIntegral_mul_ofSimpleFunc E f g
    exact fun theta ↦ congrFun hEq theta
  have hEq :
      (fun theta : BoundedMeasurableFunction X ↦ spectralIntegral E (phi * theta)) =
        fun theta ↦ spectralIntegral E phi * spectralIntegral E theta := by
    apply denseRange_ofSimpleFunc (X := X) |>.equalizer
    · have hm : Continuous (fun theta : BoundedMeasurableFunction X ↦
          phi * theta) := by
        exact continuous_id'.const_mul phi
      simpa only [Function.comp_def, spectralIntegralCLM_apply] using
        (spectralIntegralCLM E).continuous.comp hm
    · simpa only [spectralIntegralCLM_apply] using
        (spectralIntegralCLM E).continuous.const_mul (spectralIntegral E phi)
    · funext g
      exact hright g phi
  exact congrFun hEq psi

/-- The spectral integral of the constant-one function is the identity operator. -/
@[simp]
theorem spectralIntegral_one (E : ProjectionValuedMeasure X H) :
    spectralIntegral E (1 : BoundedMeasurableFunction X) = 1 := by
  calc
    spectralIntegral E (1 : BoundedMeasurableFunction X) =
        spectralIntegral E
          (BoundedMeasurableFunction.indicator (Set.univ : Set X) MeasurableSet.univ) := by
      rw [BoundedMeasurableFunction.indicator_univ]
    _ = E Set.univ := spectralIntegral_indicator E Set.univ MeasurableSet.univ
    _ = 1 := E.univ

/-- Bounded spectral integration as a unital complex star-algebra homomorphism. -/
@[no_expose]
noncomputable def spectralIntegralStarAlgHom (E : ProjectionValuedMeasure X H) :
    BoundedMeasurableFunction X →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := spectralIntegral E
  map_one' := spectralIntegral_one E
  map_mul' := spectralIntegral_mul E
  map_zero' := by
    simpa only [spectralIntegralCLM_apply] using (spectralIntegralCLM E).map_zero
  map_add' := spectralIntegral_add E
  commutes' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, spectralIntegral_smul, spectralIntegral_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := spectralIntegral_star E

@[simp]
theorem spectralIntegralStarAlgHom_apply
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    spectralIntegralStarAlgHom E phi = spectralIntegral E phi := by
  rfl

/-- Spectral integrals of two bounded measurable functions commute. -/
theorem spectralIntegral_commute
    (E : ProjectionValuedMeasure X H) (phi psi : BoundedMeasurableFunction X) :
    Commute (spectralIntegral E phi) (spectralIntegral E psi) := by
  change Commute (spectralIntegralStarAlgHom E phi) (spectralIntegralStarAlgHom E psi)
  exact (Commute.all phi psi).map (spectralIntegralStarAlgHom E)

/-- Every bounded spectral integral is a normal operator. -/
theorem spectralIntegral_isStarNormal
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    IsStarNormal (spectralIntegral E phi) := by
  constructor
  rw [← spectralIntegral_star E phi]
  exact spectralIntegral_commute E (star phi) phi

/-- Uniform convergence of bounded measurable functions along any filter implies operator-norm
convergence of their spectral integrals. -/
theorem tendsto_spectralIntegral {I : Type*} {l : Filter I}
    (E : ProjectionValuedMeasure X H) {phi : I → BoundedMeasurableFunction X}
    {psi : BoundedMeasurableFunction X} (hphi : Tendsto phi l (𝓝 psi)) :
    Tendsto (fun i ↦ spectralIntegral E (phi i)) l (𝓝 (spectralIntegral E psi)) := by
  simpa only [Function.comp_def, spectralIntegralCLM_apply] using
    ((spectralIntegralCLM E).continuous.tendsto psi).comp hphi

end

end ProjectionValuedMeasure
end MathlibExt.Analysis.InnerProductSpace
