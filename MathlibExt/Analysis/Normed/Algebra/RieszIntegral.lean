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

public import MathlibExt.Analysis.Complex.AdmissibleGrid
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.ProjIcc

/-!
# Riesz contour integration in complex normed algebras

For an element `a` of a unital complex normed algebra, the Riesz integrand is `f(z) •
(z·1-a)⁻¹`, using Mathlib's resolvent and its total inverse. The integrand definition requires
no completeness. In a complete complex normed algebra the Riesz integral over a rectilinear
cycle is this contour integral multiplied by `(2πi)⁻¹`. Multiplication need not commute, and the
zero algebra is allowed.

A finite grid filling has positive scale `t` and counterclockwise cell boundaries. Its reduced
boundary integral is additive and complex-linear for integrands continuous on the reduced trace,
is continuous under joint continuous parameter variation, and obeys Fubini without interchanging
the order of algebra factors. A uniform real bound `C` gives the norm bound
`number_of_surviving_edges / t * C`. Empty fillings have length and integral zero. Every
Banach-valued statement has the displayed complete complex normed target hypotheses.

Complex derivatives integrate to zero when the derivative relation and continuity hold on the
reduced trace. Cauchy's formula additionally assumes an open analytic domain containing the
filled region, a point in that domain off the trace, and analytic index one. The first resolvent
identity needs two resolvent points that are distinct; no completeness is needed for that
identity, and the distinctness condition protects the total scalar inverse.

Two cycles give equal Riesz integrals when their difference is filled by rectangles in the
analytic resolvent domain. In particular, admissible grid fillings around the spectrum give a
representative-independent value. The constant function one integrates to the algebra identity,
and the coordinate function integrates to `a`. Scalar values on the reduced trace determine a
fixed contour integral.

## References

John B. Conway, *A Course in Functional Analysis*, second edition, Graduate Texts in Mathematics
96, Springer, 1990, Chapter VII §4, pp. 199–204. Definition 4.5 introduces the normalized Riesz
contour integral and Proposition 4.6 gives its contour independence. The finite rectilinear-grid
integration lemmas here supply the contour calculations for that calculus; they do not assert
existence of arbitrary smooth or rectifiable contour systems.
-/

@[expose] public section


open Set Filter

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- **Resolvent-weighted scalar integrand.** Let `A` be a unital complex normed algebra with
its given norm and `a∈A`. For `f:ℂ→ℂ`, the integrand is `z↦f(z) • (z·1-a)⁻¹`, with
Mathlib's total inverse. Completeness and commutative multiplication are not required; the
zero algebra is allowed. -/
noncomputable def rieszIntegrand (a : A) (f : ℂ → ℂ) (z : ℂ) : A :=
  f z • resolvent a z

variable [CompleteSpace A]

/-- **Normalized Riesz contour integral.** Let `A` be a complete unital complex normed algebra
with its given norm and `a∈A`. For a rectilinear cycle `Γ` and `f:ℂ→ℂ`, Write
`R_Γ(a,f)=(2πi)⁻¹ • ∮_Γ f(z) • (z·1-a)⁻¹ dz`, with total inverse. The definition imposes
no regularity condition on `f`. Multiplication may be noncommutative and `A` may be zero. -/
noncomputable def rieszIntegral (Γ : RectilinearCycle) (a : A) (f : ℂ → ℂ) : A :=
  ((2 * Real.pi : ℂ) * Complex.I)⁻¹ • Γ.integral (rieszIntegrand a f)

namespace GridFilling

/-- **Zero integrand on a finite grid contour.** Let `E` be a complete complex normed vector
space and `D` a finite grid filling with positive scale `t`. Write `∮_D f` for the complex
contour integral around its counterclockwise cell boundary cycle, with internal edges
cancelled. Then `∮_D 0=0`. The filling may be empty. -/
@[simp]
theorem toCycle_integral_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) :
    D.toCycle.integral (0 : ℂ → E) = 0 := by
  rw [D.toCycle_integral_eq_reducedIntegral]
  unfold reducedIntegral
  apply Finset.sum_eq_zero
  intro e he
  cases e <;> simp [edgeIntegral]

/-- **Addition of continuous grid-contour integrands.** Let `E` be a complete complex normed
vector space and `D` a finite grid filling with positive scale `t`. Write `∮_D f` for the
complex contour integral around its counterclockwise cell boundary cycle, with internal
edges cancelled. If `f,g:ℂ→E` are continuous on the reduced trace of `D`, then
`∮_D(f+g)=∮_D f+∮_D g`. No differentiability or condition in the filled interior is
required. -/
theorem toCycle_integral_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling)
    {f g : ℂ → E} (hf : ContinuousOn f D.reducedTrace)
    (hg : ContinuousOn g D.reducedTrace) :
    D.toCycle.integral (f + g) =
      D.toCycle.integral f + D.toCycle.integral g := by
  simp only [D.toCycle_integral_eq_reducedIntegral]
  let p : ℂ → E × E := fun z ↦ (f z, g z)
  have hp : ContinuousOn p D.reducedTrace := by
    simpa [p] using hf.prodMk hg
  have hfst := D.reducedIntegral_comp_comm
    (ContinuousLinearMap.fst ℂ E E) p (fun _ hz ↦ hz) hp
  have hsnd := D.reducedIntegral_comp_comm
    (ContinuousLinearMap.snd ℂ E E) p (fun _ hz ↦ hz) hp
  have hp_integral :
      D.reducedIntegral p = (D.reducedIntegral f, D.reducedIntegral g) := by
    apply Prod.ext
    · simpa [p] using hfst.symm
    · simpa [p] using hsnd.symm
  let L : E × E →L[ℂ] E :=
    ContinuousLinearMap.fst ℂ E E + ContinuousLinearMap.snd ℂ E E
  have hL := D.reducedIntegral_comp_comm L p (fun _ hz ↦ hz) hp
  rw [hp_integral] at hL
  change D.reducedIntegral (fun z ↦ f z + g z) =
    D.reducedIntegral f + D.reducedIntegral g
  simpa [L, p] using hL

/-- **Complex scaling of a grid-contour integral.** Let `E` be a complete complex normed
vector space and `D` a finite grid filling with positive scale `t`. Write `∮_D f` for the
complex contour integral around its counterclockwise cell boundary cycle, with internal
edges cancelled. For `c∈ℂ` and `f:ℂ→E` continuous on the reduced trace, `∮_D(c • f)=c •
∮_D f`. This includes `c=0` and the empty filling. -/
theorem toCycle_integral_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (c : ℂ)
    (f : ℂ → E) (hf : ContinuousOn f D.reducedTrace) :
    D.toCycle.integral (c • f) = c • D.toCycle.integral f := by
  simp only [D.toCycle_integral_eq_reducedIntegral]
  let L : E →L[ℂ] E := c • ContinuousLinearMap.id ℂ E
  have hL := D.reducedIntegral_comp_comm L f (fun _ hz ↦ hz) hf
  change D.reducedIntegral (fun z ↦ c • f z) = c • D.reducedIntegral f
  simpa [L] using hL

private theorem continuousOn_edgeIntegral_param
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (e : GridEdge) {S : Set ℂ} (F : ℂ → ℂ → E)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ D.edgeTrace e)) :
    ContinuousOn (fun z ↦ D.edgeIntegral e (F z)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hF ⊢
  cases e with
  | horizontal v =>
      let a : ℝ := (v 0 : ℝ) / D.scale
      let b : ℝ := ((v 0 : ℝ) + 1) / D.scale
      have hab : a ≤ b := by
        dsimp [a, b]
        exact (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
      let q : ℝ → ℂ := fun x ↦
        (Set.projIcc a b hab x : ℝ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I
      have hqmem (x : ℝ) : q x ∈ D.edgeTrace (.horizontal v) := by
        apply D.horizontal_point_mem_edgeTrace v
        exact (Set.projIcc a b hab x).property
      have hjoint : Continuous (Function.uncurry fun
          (p : {p : ℂ // p ∈ S}) (x : ℝ) ↦ F p (q x)) := by
        apply hF.comp (f := fun p : {p : ℂ // p ∈ S} × ℝ ↦
          ⟨((p.1 : ℂ), q p.2), ⟨p.1.property, hqmem p.2⟩⟩)
        fun_prop
      have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) hjoint a b
      change Continuous fun p : {p : ℂ // p ∈ S} ↦
        ∫ x : ℝ in a..b,
          F p (x + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I)
      convert hcont using 1
      funext p
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hx
      change F (p : ℂ)
        ((x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I) = F p (q x)
      rw [show q x =
          (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I by
        simp [q, Set.projIcc_of_mem hab hx']]
  | vertical v =>
      let a : ℝ := (v 1 : ℝ) / D.scale
      let b : ℝ := ((v 1 : ℝ) + 1) / D.scale
      have hab : a ≤ b := by
        dsimp [a, b]
        exact (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
      let q : ℝ → ℂ := fun y ↦
        ((v 0 : ℝ) / D.scale : ℂ) + (Set.projIcc a b hab y : ℝ) * Complex.I
      have hqmem (y : ℝ) : q y ∈ D.edgeTrace (.vertical v) := by
        apply D.vertical_point_mem_edgeTrace v
        exact (Set.projIcc a b hab y).property
      have hjoint : Continuous (Function.uncurry fun
          (p : {p : ℂ // p ∈ S}) (y : ℝ) ↦ F p (q y)) := by
        apply hF.comp (f := fun p : {p : ℂ // p ∈ S} × ℝ ↦
          ⟨((p.1 : ℂ), q p.2), ⟨p.1.property, hqmem p.2⟩⟩)
        fun_prop
      have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) hjoint a b
      have hcont' : Continuous fun p : {p : ℂ // p ∈ S} ↦
          ∫ y : ℝ in a..b,
            F p (((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I) := by
        convert hcont using 1
        funext p
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : y ∈ Set.Icc a b := by
          simpa [Set.uIcc_of_le hab] using hy
        change F (p : ℂ)
          (((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I) = F p (q y)
        rw [show q y =
            ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I by
          simp [q, Set.projIcc_of_mem hab hy']]
      exact hcont'.const_smul Complex.I

/-- **Continuity of a grid integral in a complex parameter.** Let `E` be a complete complex
normed vector space and `D` a finite grid filling with positive scale `t`. Write `∮_D f`
for the complex contour integral around its counterclockwise cell boundary cycle, with
internal edges cancelled. For any `S⊆ℂ` and `F:ℂ×ℂ→E` continuous on `S×trace(D)`, the
function `z↦∮_D F(z,ζ) dζ` is continuous on `S`. Continuity is relative to these sets;
they need not be open. -/
theorem continuousOn_toCycle_integral_param
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {S : Set ℂ} (F : ℂ → ℂ → E)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ D.reducedTrace)) :
    ContinuousOn (fun z ↦ D.toCycle.integral (F z)) S := by
  have heq : (fun z ↦ D.toCycle.integral (F z)) =
      fun z ↦ D.reducedIntegral (F z) := by
    funext z
    exact D.toCycle_integral_eq_reducedIntegral (F z)
  rw [heq]
  unfold GridFilling.reducedIntegral
  apply continuousOn_finsetSum
  intro e he
  have hedge : ContinuousOn (fun z ↦ D.edgeIntegral e (F z)) S :=
    continuousOn_edgeIntegral_param D e F <|
      hF.mono <| Set.prod_mono Subset.rfl fun w hw ↦
        Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem he hw)
  have hc := hedge.const_smul (D.boundaryCoeff e : ℂ)
  change ContinuousOn (fun z ↦ (D.boundaryCoeff e : ℂ) •
    D.edgeIntegral e (F z)) S at hc
  simpa only [Int.cast_smul_eq_zsmul] using hc

private theorem edgeIntegral_finsetSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {I : Type*} (D : GridFilling) (e : GridEdge) (s : Finset I)
    (f : I → ℂ → E) (hf : ∀ i ∈ s, ContinuousOn (f i) (D.edgeTrace e)) :
    D.edgeIntegral e (fun z ↦ ∑ i ∈ s, f i z) =
      ∑ i ∈ s, D.edgeIntegral e (f i) := by
  cases e with
  | horizontal v =>
      have hint (i : I) (hi : i ∈ s) : IntervalIntegrable
          (fun x : ℝ ↦ f i
            (x + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I))
          MeasureTheory.volume ((v 0 : ℝ) / D.scale)
            (((v 0 : ℝ) + 1) / D.scale) := by
        have hpath : Continuous fun x : ℝ ↦
            (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I := by
          fun_prop
        have hcont : ContinuousOn
            (fun x : ℝ ↦ f i
              (x + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I))
            (Set.uIcc ((v 0 : ℝ) / D.scale)
              (((v 0 : ℝ) + 1) / D.scale)) := by
          apply (hf i hi).comp hpath.continuousOn
          intro x hx
          apply D.horizontal_point_mem_edgeTrace v
          have hab : (v 0 : ℝ) / D.scale ≤ ((v 0 : ℝ) + 1) / D.scale :=
            (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
          simpa [Set.uIcc_of_le hab] using hx
        exact hcont.intervalIntegrable
      simp only [edgeIntegral]
      exact intervalIntegral.integral_finsetSum hint
  | vertical v =>
      have hint (i : I) (hi : i ∈ s) : IntervalIntegrable
          (fun y : ℝ ↦ f i
            (((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I))
          MeasureTheory.volume ((v 1 : ℝ) / D.scale)
            (((v 1 : ℝ) + 1) / D.scale) := by
        have hpath : Continuous fun y : ℝ ↦
            ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I := by
          fun_prop
        have hcont : ContinuousOn
            (fun y : ℝ ↦ f i
              (((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I))
            (Set.uIcc ((v 1 : ℝ) / D.scale)
              (((v 1 : ℝ) + 1) / D.scale)) := by
          apply (hf i hi).comp hpath.continuousOn
          intro y hy
          apply D.vertical_point_mem_edgeTrace v
          have hab : (v 1 : ℝ) / D.scale ≤ ((v 1 : ℝ) + 1) / D.scale :=
            (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
          simpa [Set.uIcc_of_le hab] using hy
        exact hcont.intervalIntegrable
      simp only [edgeIntegral]
      rw [intervalIntegral.integral_finsetSum hint, Finset.smul_sum]

private theorem edgeIntegral_zsmul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (e : GridEdge) (n : ℤ) (f : ℂ → E) :
    D.edgeIntegral e (fun z ↦ n • f z) = n • D.edgeIntegral e f := by
  simp only [← Int.cast_smul_eq_zsmul ℂ]
  cases e <;> simp [edgeIntegral, smul_smul, mul_comm]

private theorem edgeIntegral_reducedIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D H : GridFilling) (e : GridEdge) (F : ℂ → ℂ → E)
    (hF : ContinuousOn (Function.uncurry F) (D.edgeTrace e ×ˢ H.reducedTrace)) :
    D.edgeIntegral e (fun z ↦ H.reducedIntegral (F z)) =
      ∑ d ∈ H.boundaryEdges,
        H.boundaryCoeff d • D.edgeIntegral e (fun z ↦ H.edgeIntegral d (F z)) := by
  change D.edgeIntegral e (fun z ↦
    ∑ d ∈ H.boundaryEdges, H.boundaryCoeff d • H.edgeIntegral d (F z)) = _
  calc
    _ = ∑ d ∈ H.boundaryEdges, D.edgeIntegral e
        (fun z ↦ H.boundaryCoeff d • H.edgeIntegral d (F z)) := by
      apply edgeIntegral_finsetSum
      intro d hd
      have hparam : ContinuousOn (fun z ↦ H.edgeIntegral d (F z))
          (D.edgeTrace e) :=
        continuousOn_edgeIntegral_param H d F <|
          hF.mono <| Set.prod_mono Subset.rfl fun w hw ↦
            Set.mem_iUnion_of_mem d (Set.mem_iUnion_of_mem hd hw)
      have hc := hparam.const_smul (H.boundaryCoeff d : ℂ)
      change ContinuousOn (fun z ↦ (H.boundaryCoeff d : ℂ) •
        H.edgeIntegral d (F z)) (D.edgeTrace e) at hc
      simpa only [Int.cast_smul_eq_zsmul] using hc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      exact edgeIntegral_zsmul D e (H.boundaryCoeff d)
        (fun z ↦ H.edgeIntegral d (F z))

private theorem intervalIntegral_intervalIntegral_swap_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : ℝ → ℝ → E} {a b c d : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.uIcc a b ×ˢ Set.uIcc c d)) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in c..d, F x y) =
      ∫ y : ℝ in c..d, ∫ x : ℝ in a..b, F x y := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  exact (hF.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

private theorem edgeIntegral_edgeIntegral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D H : GridFilling) (e e' : GridEdge) (F : ℂ → ℂ → E)
    (hF : ContinuousOn (Function.uncurry F) (D.edgeTrace e ×ˢ H.edgeTrace e')) :
    D.edgeIntegral e (fun z ↦ H.edgeIntegral e' (F z)) =
      H.edgeIntegral e' (fun ζ ↦ D.edgeIntegral e (fun z ↦ F z ζ)) := by
  have swap_paths (a b c d : ℝ) (p q : ℝ → ℂ)
      (hp : Continuous p) (hq : Continuous q)
      (hpmem : Set.MapsTo p (Set.uIcc a b) (D.edgeTrace e))
      (hqmem : Set.MapsTo q (Set.uIcc c d) (H.edgeTrace e')) :
      (∫ x : ℝ in a..b, ∫ y : ℝ in c..d, F (p x) (q y)) =
        ∫ y : ℝ in c..d, ∫ x : ℝ in a..b, F (p x) (q y) := by
    apply intervalIntegral_intervalIntegral_swap_of_continuousOn
    apply hF.comp ((hp.comp continuous_fst).prodMk
      (hq.comp continuous_snd)).continuousOn
    intro x hx
    exact ⟨hpmem hx.1, hqmem hx.2⟩
  cases e with
  | horizontal v =>
      let a : ℝ := (v 0 : ℝ) / D.scale
      let b : ℝ := ((v 0 : ℝ) + 1) / D.scale
      have hab : a ≤ b := by
        dsimp [a, b]
        exact (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
      let p : ℝ → ℂ := fun x ↦
        (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I
      have hp : Continuous p := by fun_prop
      have hpmem : Set.MapsTo p (Set.uIcc a b)
          (D.edgeTrace (.horizontal v)) := by
        intro x hx
        apply D.horizontal_point_mem_edgeTrace v
        simpa [a, b, Set.uIcc_of_le hab] using hx
      cases e' with
      | horizontal w =>
          let c : ℝ := (w 0 : ℝ) / H.scale
          let d : ℝ := ((w 0 : ℝ) + 1) / H.scale
          have hcd : c ≤ d := by
            dsimp [c, d]
            exact (div_le_div_iff_of_pos_right H.scale_pos).2 (by norm_num)
          let q : ℝ → ℂ := fun y ↦
            (y : ℂ) + ((w 1 : ℝ) / H.scale : ℂ) * Complex.I
          have hq : Continuous q := by fun_prop
          have hqmem : Set.MapsTo q (Set.uIcc c d)
              (H.edgeTrace (.horizontal w)) := by
            intro y hy
            apply H.horizontal_point_mem_edgeTrace w
            simpa [c, d, Set.uIcc_of_le hcd] using hy
          simpa [edgeIntegral, p, q, a, b, c, d] using
            swap_paths a b c d p q hp hq hpmem hqmem
      | vertical w =>
          let c : ℝ := (w 1 : ℝ) / H.scale
          let d : ℝ := ((w 1 : ℝ) + 1) / H.scale
          have hcd : c ≤ d := by
            dsimp [c, d]
            exact (div_le_div_iff_of_pos_right H.scale_pos).2 (by norm_num)
          let q : ℝ → ℂ := fun y ↦
            ((w 0 : ℝ) / H.scale : ℂ) + (y : ℂ) * Complex.I
          have hq : Continuous q := by fun_prop
          have hqmem : Set.MapsTo q (Set.uIcc c d)
              (H.edgeTrace (.vertical w)) := by
            intro y hy
            apply H.vertical_point_mem_edgeTrace w
            simpa [c, d, Set.uIcc_of_le hcd] using hy
          have hswap := swap_paths a b c d p q hp hq hpmem hqmem
          simpa [edgeIntegral, p, q, a, b, c, d] using
            congrArg (fun x : E ↦ Complex.I • x) hswap
  | vertical v =>
      let a : ℝ := (v 1 : ℝ) / D.scale
      let b : ℝ := ((v 1 : ℝ) + 1) / D.scale
      have hab : a ≤ b := by
        dsimp [a, b]
        exact (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
      let p : ℝ → ℂ := fun x ↦
        ((v 0 : ℝ) / D.scale : ℂ) + (x : ℂ) * Complex.I
      have hp : Continuous p := by fun_prop
      have hpmem : Set.MapsTo p (Set.uIcc a b)
          (D.edgeTrace (.vertical v)) := by
        intro x hx
        apply D.vertical_point_mem_edgeTrace v
        simpa [a, b, Set.uIcc_of_le hab] using hx
      cases e' with
      | horizontal w =>
          let c : ℝ := (w 0 : ℝ) / H.scale
          let d : ℝ := ((w 0 : ℝ) + 1) / H.scale
          have hcd : c ≤ d := by
            dsimp [c, d]
            exact (div_le_div_iff_of_pos_right H.scale_pos).2 (by norm_num)
          let q : ℝ → ℂ := fun y ↦
            (y : ℂ) + ((w 1 : ℝ) / H.scale : ℂ) * Complex.I
          have hq : Continuous q := by fun_prop
          have hqmem : Set.MapsTo q (Set.uIcc c d)
              (H.edgeTrace (.horizontal w)) := by
            intro y hy
            apply H.horizontal_point_mem_edgeTrace w
            simpa [c, d, Set.uIcc_of_le hcd] using hy
          have hswap := swap_paths a b c d p q hp hq hpmem hqmem
          simpa [edgeIntegral, p, q, a, b, c, d] using
            congrArg (fun x : E ↦ Complex.I • x) hswap
      | vertical w =>
          let c : ℝ := (w 1 : ℝ) / H.scale
          let d : ℝ := ((w 1 : ℝ) + 1) / H.scale
          have hcd : c ≤ d := by
            dsimp [c, d]
            exact (div_le_div_iff_of_pos_right H.scale_pos).2 (by norm_num)
          let q : ℝ → ℂ := fun y ↦
            ((w 0 : ℝ) / H.scale : ℂ) + (y : ℂ) * Complex.I
          have hq : Continuous q := by fun_prop
          have hqmem : Set.MapsTo q (Set.uIcc c d)
              (H.edgeTrace (.vertical w)) := by
            intro y hy
            apply H.vertical_point_mem_edgeTrace w
            simpa [c, d, Set.uIcc_of_le hcd] using hy
          have hswap := swap_paths a b c d p q hp hq hpmem hqmem
          simpa [edgeIntegral, p, q, a, b, c, d] using
            congrArg (fun x : E ↦ Complex.I • (Complex.I • x)) hswap

/-- **Fubini equality for two finite grid contours.** Let `E` be a complete complex normed
vector space and `D` a finite grid filling with positive scale `t`. Let `H` be another
finite grid filling. If `F:ℂ×ℂ→E` is jointly continuous on `trace(D)×trace(H)`, then `∮_D
[∮_H F(z,ζ) dζ] dz=∮_H [∮_D F(z,ζ) dz] dζ`. The arguments of `F` retain their order; no
algebra product is exchanged. -/
theorem toCycle_integral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D H : GridFilling) (F : ℂ → ℂ → E)
    (hF : ContinuousOn (Function.uncurry F)
      (D.reducedTrace ×ˢ H.reducedTrace)) :
    D.toCycle.integral (fun z ↦ H.toCycle.integral (F z)) =
      H.toCycle.integral (fun ζ ↦ D.toCycle.integral (fun z ↦ F z ζ)) := by
  simp only [GridFilling.toCycle_integral_eq_reducedIntegral]
  let Fswap : ℂ → ℂ → E := fun ζ z ↦ F z ζ
  have hFswap : ContinuousOn (Function.uncurry Fswap)
      (H.reducedTrace ×ˢ D.reducedTrace) := by
    have hswap : Continuous fun x : ℂ × ℂ ↦ (x.2, x.1) :=
      continuous_snd.prodMk continuous_fst
    change ContinuousOn (fun x : ℂ × ℂ ↦ F x.2 x.1)
      (H.reducedTrace ×ˢ D.reducedTrace)
    exact hF.comp hswap.continuousOn (fun x hx ↦ ⟨hx.2, hx.1⟩)
  change
    (∑ e ∈ D.boundaryEdges, D.boundaryCoeff e •
      D.edgeIntegral e (fun z ↦ H.reducedIntegral (F z))) =
    ∑ d ∈ H.boundaryEdges, H.boundaryCoeff d •
      H.edgeIntegral d (fun ζ ↦ D.reducedIntegral (fun z ↦ F z ζ))
  calc
    _ = ∑ e ∈ D.boundaryEdges, D.boundaryCoeff e •
        ∑ d ∈ H.boundaryEdges, H.boundaryCoeff d •
          D.edgeIntegral e (fun z ↦ H.edgeIntegral d (F z)) := by
      apply Finset.sum_congr rfl
      intro e he
      apply congrArg (fun x : E ↦ D.boundaryCoeff e • x)
      apply edgeIntegral_reducedIntegral
      exact hF.mono <| Set.prod_mono
        (fun z hz ↦ Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem he hz)) Subset.rfl
    _ = ∑ e ∈ D.boundaryEdges, D.boundaryCoeff e •
        ∑ d ∈ H.boundaryEdges, H.boundaryCoeff d •
          H.edgeIntegral d (fun ζ ↦ D.edgeIntegral e (fun z ↦ F z ζ)) := by
      apply Finset.sum_congr rfl
      intro e he
      apply congrArg (fun x : E ↦ D.boundaryCoeff e • x)
      apply Finset.sum_congr rfl
      intro d hd
      apply congrArg (fun x : E ↦ H.boundaryCoeff d • x)
      apply edgeIntegral_edgeIntegral_swap
      exact hF.mono <| Set.prod_mono
        (fun z hz ↦ Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem he hz))
        (fun z hz ↦ Set.mem_iUnion_of_mem d (Set.mem_iUnion_of_mem hd hz))
    _ = ∑ d ∈ H.boundaryEdges, H.boundaryCoeff d •
        ∑ e ∈ D.boundaryEdges, D.boundaryCoeff e •
          H.edgeIntegral d (fun ζ ↦ D.edgeIntegral e (fun z ↦ F z ζ)) := by
      simp_rw [Finset.smul_sum]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      simp [smul_smul, mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply congrArg (fun x : E ↦ H.boundaryCoeff d • x)
      symm
      simpa [Fswap] using edgeIntegral_reducedIntegral H D d Fswap
        (hFswap.mono <| Set.prod_mono
          (fun z hz ↦ Set.mem_iUnion_of_mem d (Set.mem_iUnion_of_mem hd hz)) Subset.rfl)

/-- **Length bound for a grid-contour integral.** Let `E` be a complete complex normed vector
space and `D` a finite grid filling with positive scale `t`. Write `∮_D f` for the complex
contour integral around its counterclockwise cell boundary cycle, with internal edges
cancelled. Let `b` be the number of surviving boundary edges. If `C∈ℝ` and `‖f(z)‖≤C` on
the reduced trace, then `‖∮_D f‖≤(b/t)C`. No continuity premise is required by this bound.
For an empty filling, both the integral and `b/t` are zero; no separate `C≥0` assumption
is made. -/
theorem norm_toCycle_integral_le_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {f : ℂ → E} {C : ℝ}
    (hf : ∀ z ∈ D.reducedTrace, ‖f z‖ ≤ C) :
    ‖D.toCycle.integral f‖ ≤
      ((D.boundaryEdges.card : ℝ) / D.scale) * C := by
  rw [D.toCycle_integral_eq_reducedIntegral]
  unfold reducedIntegral
  have hedge (e : GridEdge) (he : e ∈ D.boundaryEdges) :
      ‖D.edgeIntegral e f‖ ≤ C / D.scale := by
    cases e with
    | horizontal v =>
        have hab : (v 0 : ℝ) / D.scale ≤ ((v 0 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        have hlen :
            |((v 0 : ℝ) + 1) / D.scale - (v 0 : ℝ) / D.scale| =
              1 / D.scale := by
          rw [show ((v 0 : ℝ) + 1) / D.scale - (v 0 : ℝ) / D.scale =
              1 / D.scale by
            field_simp [D.scale_pos.ne']
            ring]
          exact abs_of_pos (one_div_pos.mpr D.scale_pos)
        calc
          ‖D.edgeIntegral (.horizontal v) f‖ ≤
              C * |((v 0 : ℝ) + 1) / D.scale - (v 0 : ℝ) / D.scale| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro x hx
            apply hf
            apply mem_iUnion_of_mem (.horizontal v)
            apply mem_iUnion_of_mem he
            apply D.horizontal_point_mem_edgeTrace v
            simpa [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hx
          _ = C / D.scale := by rw [hlen]; ring
    | vertical v =>
        have hab : (v 1 : ℝ) / D.scale ≤ ((v 1 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        have hlen :
            |((v 1 : ℝ) + 1) / D.scale - (v 1 : ℝ) / D.scale| =
              1 / D.scale := by
          rw [show ((v 1 : ℝ) + 1) / D.scale - (v 1 : ℝ) / D.scale =
              1 / D.scale by
            field_simp [D.scale_pos.ne']
            ring]
          exact abs_of_pos (one_div_pos.mpr D.scale_pos)
        calc
          ‖D.edgeIntegral (.vertical v) f‖ =
              ‖∫ y : ℝ in (v 1 : ℝ) / D.scale..((v 1 : ℝ) + 1) / D.scale,
                f (((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I)‖ := by
            simp [edgeIntegral, norm_smul]
          _ ≤ C * |((v 1 : ℝ) + 1) / D.scale - (v 1 : ℝ) / D.scale| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro y hy
            apply hf
            apply mem_iUnion_of_mem (.vertical v)
            apply mem_iUnion_of_mem he
            apply D.vertical_point_mem_edgeTrace v
            simpa [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hy
          _ = C / D.scale := by rw [hlen]; ring
  have hterm (e : GridEdge) (he : e ∈ D.boundaryEdges) :
      ‖D.boundaryCoeff e • D.edgeIntegral e f‖ ≤ C / D.scale := by
    rcases D.boundaryCoeff_eq_one_or_neg_one_of_mem he with h | h
    · simpa [h] using hedge e he
    · simpa [h] using hedge e he
  calc
    ‖∑ e ∈ D.boundaryEdges, D.boundaryCoeff e • D.edgeIntegral e f‖ ≤
        ∑ e ∈ D.boundaryEdges,
          ‖D.boundaryCoeff e • D.edgeIntegral e f‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ D.boundaryEdges, C / D.scale := by
      apply Finset.sum_le_sum
      intro e he
      exact hterm e he
    _ = ((D.boundaryEdges.card : ℝ) / D.scale) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- **A complex derivative has zero grid-contour integral.** Let `E` be a complete complex
normed vector space and `D` a finite grid filling with positive scale `t`. Write `∮_D f`
for the complex contour integral around its counterclockwise cell boundary cycle, with
internal edges cancelled. Let `F,f:ℂ→E`. If `f` is continuous on the reduced trace and `F`
has complex derivative `f(z)` at every point `z` of that trace, then `∮_D f=0`. No
derivative hypothesis is imposed in the interior. -/
theorem toCycle_integral_eq_zero_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {F f : ℂ → E}
    (hf : ContinuousOn f D.reducedTrace)
    (hF : ∀ z ∈ D.reducedTrace, HasDerivAt F (f z) z) :
    D.toCycle.integral f = 0 := by
  classical
  have hedge (e : GridEdge) (he : e ∈ D.boundaryEdges) :
      D.edgeIntegral e f = F (D.edgeEnd e) - F (D.edgeStart e) := by
    cases e with
    | horizontal v =>
        have hab : (v 0 : ℝ) / D.scale ≤ ((v 0 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        let γ : ℝ → ℂ := fun x ↦
          (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I
        have hγmem {x : ℝ}
            (hx : x ∈ Set.uIcc ((v 0 : ℝ) / D.scale)
              (((v 0 : ℝ) + 1) / D.scale)) : γ x ∈ D.reducedTrace := by
          apply mem_iUnion_of_mem (.horizontal v)
          apply mem_iUnion_of_mem he
          apply D.horizontal_point_mem_edgeTrace v
          simpa [γ, Set.uIcc_of_le hab] using hx
        have hcont : ContinuousOn (fun x ↦ f (γ x))
            (Set.uIcc ((v 0 : ℝ) / D.scale)
              (((v 0 : ℝ) + 1) / D.scale)) := by
          apply hf.comp (by fun_prop)
          exact fun x hx ↦ hγmem hx
        have hderiv (x : ℝ)
            (hx : x ∈ Set.uIcc ((v 0 : ℝ) / D.scale)
              (((v 0 : ℝ) + 1) / D.scale)) :
            HasDerivAt (fun y ↦ F (γ y)) (f (γ x)) x := by
          have hγ : HasDerivAt γ (1 : ℂ) x := by
            simpa [γ] using
              (Complex.ofRealCLM.hasDerivAt (x := x)).add_const
                (((v 1 : ℝ) / D.scale : ℂ) * Complex.I)
          simpa [Function.comp_def] using (hF (γ x) (hγmem hx)).scomp x hγ
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          hcont.intervalIntegrable
        simpa [edgeIntegral, edgeStart, edgeEnd, point, gridPoint,
          GridIndex.succ, γ] using hFTC
    | vertical v =>
        have hab : (v 1 : ℝ) / D.scale ≤ ((v 1 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        let γ : ℝ → ℂ := fun y ↦
          ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I
        have hγmem {y : ℝ}
            (hy : y ∈ Set.uIcc ((v 1 : ℝ) / D.scale)
              (((v 1 : ℝ) + 1) / D.scale)) : γ y ∈ D.reducedTrace := by
          apply mem_iUnion_of_mem (.vertical v)
          apply mem_iUnion_of_mem he
          apply D.vertical_point_mem_edgeTrace v
          simpa [γ, Set.uIcc_of_le hab] using hy
        have hcont : ContinuousOn (fun y ↦ f (γ y))
            (Set.uIcc ((v 1 : ℝ) / D.scale)
              (((v 1 : ℝ) + 1) / D.scale)) := by
          apply hf.comp (by fun_prop)
          exact fun y hy ↦ hγmem hy
        have hderiv (y : ℝ)
            (hy : y ∈ Set.uIcc ((v 1 : ℝ) / D.scale)
              (((v 1 : ℝ) + 1) / D.scale)) :
            HasDerivAt (fun x ↦ F (γ x))
              (Complex.I • f (γ y)) y := by
          have hγ : HasDerivAt γ Complex.I y := by
            simpa [γ] using
              ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add
                ((v 0 : ℝ) / D.scale : ℂ)
          simpa [Function.comp_def] using (hF (γ y) (hγmem hy)).scomp y hγ
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          (hcont.const_smul Complex.I).intervalIntegrable
        rw [intervalIntegral.integral_smul] at hFTC
        simpa [edgeIntegral, edgeStart, edgeEnd, point, gridPoint,
          GridIndex.succ, γ] using hFTC
  let endpointAddHom : (GridEdge →₀ ℤ) →+ E :=
    { toFun := fun c ↦ c.sum fun e n ↦
        n • (F (D.edgeEnd e) - F (D.edgeStart e))
      map_zero' := by simp
      map_add' := by
        intro c d
        apply Finsupp.sum_add_index'
        · intro e
          simp
        · intro e m n
          simp [add_zsmul] }
  have hcell (v : GridIndex) : endpointAddHom (cellBoundaryChain v) = 0 := by
    have hsucc : (v.succ 1).succ 0 = (v.succ 0).succ 1 := by
      funext i
      fin_cases i <;> simp [GridIndex.succ]
    rw [cellBoundaryChain, map_sub, map_add, map_sub]
    simp [endpointAddHom, edgeStart, edgeEnd, hsucc]
    abel
  rw [D.toCycle_integral_eq_reducedIntegral]
  unfold reducedIntegral
  calc
    ∑ e ∈ D.boundaryEdges, D.boundaryCoeff e • D.edgeIntegral e f =
        ∑ e ∈ D.boundaryEdges,
          D.boundaryCoeff e • (F (D.edgeEnd e) - F (D.edgeStart e)) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hedge e he]
    _ = endpointAddHom D.boundaryChain := by
      rw [D.boundaryEdges_eq_boundaryChain_support]
      have hcoeff (e : GridEdge) : D.boundaryCoeff e = D.boundaryChain e := by
        cases e <;> simp
      simp_rw [hcoeff]
      rfl
    _ = 0 := by
      rw [boundaryChain, map_sum]
      apply Finset.sum_eq_zero
      intro v hv
      exact hcell v

/-- **Scalar Cauchy theorem on a filled grid region.** Let `D` be a positive-scale finite grid
filling and `f:ℂ→ℂ` complex differentiable on its entire filled region. Then
`D.toCycle.integral f=0`. The hypothesis is differentiability on the region, including its
boundary; no larger open domain is a premise. -/
theorem toCycle_integral_eq_zero_of_differentiableOn_region
    (D : GridFilling) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D.region) :
    D.toCycle.integral f = 0 := by
  rw [D.toCycle_integral]
  apply Finset.sum_eq_zero
  intro v hv
  apply (D.cell v).boundaryIntegral_eq_zero
  exact hf.mono fun z hz ↦
    Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv hz)

/-- **Cauchy evaluation formula for a grid contour.** Let `D` be a positive-scale finite grid
filling, `G⊆ℂ` open with `D.region⊆G`, and `f:ℂ→ℂ` complex differentiable on `G`. If `z∈G`
is off the reduced trace and `D.toCycle.index z=1`, then `(2πi)⁻¹∮_D f(ζ)(ζ-z)⁻¹ dζ=f(z)`.
The contour index specifies the positive orientation. -/
theorem toCycle_cauchy_formula
    (D : GridFilling) {G : Set ℂ} (hG : IsOpen G) (hDG : D.region ⊆ G)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f G) {z : ℂ}
    (hzG : z ∈ G) (hztrace : z ∉ D.reducedTrace)
    (hindex : D.toCycle.index z = 1) :
    ((2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        D.toCycle.integral (fun ζ ↦ f ζ * (ζ - z)⁻¹) = f z := by
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  let q : ℂ → ℂ := dslope f z
  let k : ℂ → ℂ := fun ζ ↦ (ζ - z)⁻¹
  have htraceG : D.reducedTrace ⊆ G := D.reducedTrace_subset_region.trans hDG
  have hqdiff : DifferentiableOn ℂ q G := by
    exact (Complex.differentiableOn_dslope (hG.mem_nhds hzG)).2 hf
  have hqcont : ContinuousOn q D.reducedTrace :=
    hqdiff.continuousOn.mono htraceG
  have hkcont : ContinuousOn k D.reducedTrace := by
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro ζ hζ
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hztrace)
  have hconstcont : ContinuousOn (fun ζ ↦ f z * k ζ) D.reducedTrace :=
    continuousOn_const.mul hkcont
  have hdecomp : Set.EqOn
      (fun ζ ↦ f ζ * k ζ)
      (fun ζ ↦ q ζ + f z * k ζ) D.reducedTrace := by
    intro ζ hζ
    have hζz : ζ ≠ z := ne_of_mem_of_not_mem hζ hztrace
    dsimp [q, k]
    rw [dslope_of_ne f hζz, slope_def_field, div_eq_mul_inv]
    ring
  have hintegral :
      D.toCycle.integral (fun ζ ↦ f ζ * k ζ) =
        D.toCycle.integral (fun ζ ↦ q ζ + f z * k ζ) := by
    simpa only [D.toCycle_integral_eq_reducedIntegral] using
      D.reducedIntegral_congr hdecomp
  have hadd :
      D.toCycle.integral (fun ζ ↦ q ζ + f z * k ζ) =
        D.toCycle.integral q +
          D.toCycle.integral (fun ζ ↦ f z * k ζ) := by
    have hadd' := D.toCycle_integral_add hqcont hconstcont
    change D.toCycle.integral (fun ζ ↦ q ζ + f z * k ζ) =
      D.toCycle.integral q +
        D.toCycle.integral (fun ζ ↦ f z * k ζ) at hadd'
    exact hadd'
  have hzero : D.toCycle.integral q = 0 :=
    D.toCycle_integral_eq_zero_of_differentiableOn_region
      (hqdiff.mono hDG)
  have hconst :
      D.toCycle.integral (fun ζ ↦ f z * k ζ) =
        f z * D.toCycle.integral k := by
    have hconst' := D.toCycle_integral_smul (f z) k hkcont
    change D.toCycle.integral (fun ζ ↦ f z • k ζ) =
      f z • D.toCycle.integral k at hconst'
    simpa only [smul_eq_mul] using hconst'
  have hindex' : c⁻¹ * D.toCycle.integral k = 1 := by
    simpa [c, k, RectilinearCycle.index] using hindex
  change c⁻¹ * D.toCycle.integral (fun ζ ↦ f ζ * k ζ) = f z
  calc
    _ = c⁻¹ * D.toCycle.integral (fun ζ ↦ q ζ + f z * k ζ) := by
      rw [hintegral]
    _ = c⁻¹ * (D.toCycle.integral q +
        D.toCycle.integral (fun ζ ↦ f z * k ζ)) := by
      rw [hadd]
    _ = c⁻¹ * (0 + f z * D.toCycle.integral k) := by
      rw [hzero, hconst]
    _ = f z * (c⁻¹ * D.toCycle.integral k) := by ring
    _ = f z := by rw [hindex', mul_one]

/-- **Vanishing integral of a nonresidual Laurent monomial.** For a positive-scale finite grid
filling `D` whose reduced trace avoids zero and an integer `m≠-1`, `∮_D z^m dz=0`.
Negative powers use the total complex inverse; avoidance of zero gives the derivative
relation on the contour. -/
private theorem toCycle_integral_zpow_eq_zero (D : GridFilling) {m : ℤ}
    (hm : m ≠ -1) (hzero : (0 : ℂ) ∉ D.reducedTrace) :
    D.toCycle.integral (fun z : ℂ ↦ z ^ m) = 0 := by
  have hz_ne (z : ℂ) (hz : z ∈ D.reducedTrace) : z ≠ 0 := by
    intro hz0
    exact hzero (hz0 ▸ hz)
  have hcont : ContinuousOn (fun z : ℂ ↦ z ^ m) D.reducedTrace :=
    (continuousOn_zpow₀ m).mono fun z hz ↦ by
      simpa only [mem_compl_iff, mem_singleton_iff] using hz_ne z hz
  refine D.toCycle_integral_eq_zero_of_hasDerivAt
    (F := fun z : ℂ ↦ z ^ (m + 1) / (m + 1)) hcont ?_
  intro z hz
  convert! (hasDerivAt_zpow (m + 1) z (Or.inl (hz_ne z hz))).div_const
    (m + 1) using 1
  have hm1 : (m + 1 : ℂ) ≠ 0 := by
    rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg,
      Int.cast_inj]
  simp [mul_div_cancel_left₀ _ hm1]

end GridFilling

private theorem toCycle_integral_smul_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → ℂ) (x : E)
    (hf : ContinuousOn f D.reducedTrace) :
    D.toCycle.integral (fun z ↦ f z • x) = D.toCycle.integral f • x := by
  rw [D.toCycle_integral_eq_reducedIntegral,
    D.toCycle_integral_eq_reducedIntegral]
  simpa using D.reducedIntegral_comp_comm
    (ContinuousLinearMap.toSpanSingleton ℂ x) f (fun _ hz ↦ hz) hf

private theorem toCycle_integral_finsetSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {J : Type*} (D : GridFilling) (s : Finset J) (f : J → ℂ → E)
    (hf : ∀ j ∈ s, ContinuousOn (f j) D.reducedTrace) :
    D.toCycle.integral (fun z ↦ ∑ j ∈ s, f j z) =
      ∑ j ∈ s, D.toCycle.integral (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change D.toCycle.integral (0 : ℂ → E) = 0
      exact D.toCycle_integral_zero
  | @insert j s hjs ih =>
      have hfj : ContinuousOn (f j) D.reducedTrace :=
        hf j (Finset.mem_insert_self j s)
      have hfs : ContinuousOn (fun z ↦ ∑ k ∈ s, f k z) D.reducedTrace := by
        exact continuousOn_finsetSum s fun k hk ↦
          hf k (Finset.mem_insert_of_mem hk)
      simp only [Finset.sum_insert hjs]
      change D.toCycle.integral (f j + fun z ↦ ∑ k ∈ s, f k z) = _
      rw [D.toCycle_integral_add hfj hfs, ih]
      intro k hk
      exact hf k (Finset.mem_insert_of_mem hk)

/-- **Finite Neumann expansion with an ordered resolvent remainder.** Let `A` be a complete
unital complex normed algebra with its given norm and `a∈A`. For `z≠0`, `‖z⁻¹ • a‖<1`, and
`N∈ℕ`, `(z·1-a)⁻¹=∑_{n<N} z^{-(n+1)} • a^n + (z⁻¹ • a)^N * (z·1-a)⁻¹`. The remainder power
multiplies the resolvent on the left. The formula includes `N=0` and noncommutative or
zero algebras. -/
private theorem resolvent_eq_finsetSum_zpow_add_remainder
    (a : A) (z : ℂ) (hz : z ≠ 0) (N : ℕ)
    (hsmall : ‖z⁻¹ • a‖ < 1) :
    resolvent a z =
      (∑ n ∈ Finset.range N, z ^ (Int.negSucc n) • a ^ n) +
        (z⁻¹ • a) ^ N * resolvent a z := by
  let u : ℂˣ := Units.mk0 z hz
  have hscale :
      resolvent a z = z⁻¹ • Ring.inverse (1 - z⁻¹ • a) := by
    have hu := spectrum.units_smul_resolvent_self (r := u) (a := a)
    have hu' := congrArg (fun x : A ↦ ((u⁻¹ : ℂ) • x)) hu
    simpa [u, Units.smul_def, resolvent, smul_smul,
      inv_mul_cancel₀ hz] using hu'
  have hgeom :
      Ring.inverse (1 - z⁻¹ • a) =
        (∑ n ∈ Finset.range N, (z⁻¹ • a) ^ n) +
          (z⁻¹ • a) ^ N * Ring.inverse (1 - z⁻¹ • a) :=
    NormedRing.inverse_one_sub_nth_order' N hsmall
  have hterm (n : ℕ) :
      z⁻¹ • (z⁻¹ • a) ^ n = z ^ (Int.negSucc n) • a ^ n := by
    rw [smul_pow, smul_smul, zpow_negSucc, ← inv_pow, pow_succ']
  have hrem :
      z⁻¹ • ((z⁻¹ • a) ^ N * Ring.inverse (1 - z⁻¹ • a)) =
        (z⁻¹ • a) ^ N * resolvent a z := by
    calc
      z⁻¹ • ((z⁻¹ • a) ^ N * Ring.inverse (1 - z⁻¹ • a)) =
          (z⁻¹ • a) ^ N *
            (z⁻¹ • Ring.inverse (1 - z⁻¹ • a)) :=
        (Algebra.mul_smul_comm _ _ _).symm
      _ = (z⁻¹ • a) ^ N * resolvent a z := by rw [← hscale]
  calc
    resolvent a z = z⁻¹ • Ring.inverse (1 - z⁻¹ • a) := hscale
    _ = z⁻¹ • ((∑ n ∈ Finset.range N, (z⁻¹ • a) ^ n) +
        (z⁻¹ • a) ^ N * Ring.inverse (1 - z⁻¹ • a)) :=
      congrArg (fun x : A ↦ z⁻¹ • x) hgeom
    _ = (∑ n ∈ Finset.range N, z ^ (Int.negSucc n) • a ^ n) +
        (z⁻¹ • a) ^ N * resolvent a z := by
      rw [smul_add, Finset.smul_sum, hrem]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro n hn
        exact hterm n
      · rfl

private theorem norm_resolvent_le_of_two_mul_norm_lt
    (a : A) (z : ℂ) (hz : 2 * ‖a‖ < ‖z‖) :
    ‖resolvent a z‖ ≤ ‖z‖⁻¹ * (‖(1 : A)‖ + 1) := by
  have hzpos : 0 < ‖z‖ := (mul_nonneg (by norm_num) (norm_nonneg a)).trans_lt hz
  have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
  have hhalf : ‖z⁻¹ • a‖ < (2 : ℝ)⁻¹ := by
    rw [norm_smul, norm_inv, inv_mul_lt_iff₀ hzpos]
    nlinarith
  have hone : ‖z⁻¹ • a‖ < 1 := hhalf.trans (by norm_num)
  have hinv_eq :
      Ring.inverse (1 - z⁻¹ • a) = ∑' n : ℕ, (z⁻¹ • a) ^ n :=
    NormedRing.inverse_one_sub (z⁻¹ • a) hone
  have hinv :
      ‖Ring.inverse (1 - z⁻¹ • a)‖ ≤ ‖(1 : A)‖ + 1 := by
    calc
      ‖Ring.inverse (1 - z⁻¹ • a)‖ = ‖∑' n : ℕ, (z⁻¹ • a) ^ n‖ := by
        rw [hinv_eq]
      _ ≤ ‖(1 : A)‖ - 1 + (1 - ‖z⁻¹ • a‖)⁻¹ :=
        tsum_geometric_le_of_norm_lt_one _ hone
      _ ≤ ‖(1 : A)‖ + 1 := by
        have htwo : (1 - ‖z⁻¹ • a‖)⁻¹ ≤ 2 :=
          inv_le_of_inv_le₀ (by norm_num) (by linarith)
        linarith
  let u : ℂˣ := Units.mk0 z hzne
  have hscale :
      resolvent a z = z⁻¹ • Ring.inverse (1 - z⁻¹ • a) := by
    have hu := spectrum.units_smul_resolvent_self (r := u) (a := a)
    have hu' := congrArg (fun x : A ↦ ((u⁻¹ : ℂ) • x)) hu
    simpa [u, Units.smul_def, resolvent, smul_smul,
      inv_mul_cancel₀ hzne] using hu'
  calc
    ‖resolvent a z‖ = ‖z⁻¹‖ * ‖Ring.inverse (1 - z⁻¹ • a)‖ := by
      rw [hscale, norm_smul]
    _ ≤ ‖z⁻¹‖ * (‖(1 : A)‖ + 1) :=
      mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = ‖z‖⁻¹ * (‖(1 : A)‖ + 1) := by rw [norm_inv]

private theorem toCycle_integral_inv_eq_two_pi_I
    (D : GridFilling) {K G : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hzero : (0 : ℂ) ∈ K) :
    D.toCycle.integral (fun z : ℂ ↦ z⁻¹) =
      (2 * Real.pi : ℂ) * Complex.I := by
  have hindex := hD.2.1 0 hzero
  rw [RectilinearCycle.index] at hindex
  simp only [sub_zero] at hindex
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast Real.two_pi_pos.ne') Complex.I_ne_zero
  simpa [c] using (inv_mul_eq_iff_eq_mul₀ hc).mp hindex
omit [CompleteSpace A] in
/-- **Ordered first resolvent identity.** Let `A` be a unital complex normed algebra with its
given norm and `a∈A`. If `z,ζ∈resolventSet ℂ a` and `z≠ζ`, then `(z·1-a)⁻¹ *
(ζ·1-a)⁻¹=(ζ-z)⁻¹ • [(z·1-a)⁻¹-(ζ·1-a)⁻¹]`. The two resolvent factors retain their
displayed order. No completeness or nonzero-algebra assumption is needed. -/
theorem resolvent_mul_resolvent {a : A} {z ζ : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hζ : ζ ∈ resolventSet ℂ a)
    (hzζ : z ≠ ζ) :
    resolvent a z * resolvent a ζ =
      (ζ - z)⁻¹ • (resolvent a z - resolvent a ζ) := by
  let x : A := algebraMap ℂ A z - a
  let y : A := algebraMap ℂ A ζ - a
  have hx : IsUnit x := by
    exact spectrum.mem_resolventSet_iff.mp hz
  have hy : IsUnit y := by
    exact spectrum.mem_resolventSet_iff.mp hζ
  have hresz : resolvent a z = Ring.inverse x := by rfl
  have hresζ : resolvent a ζ = Ring.inverse y := by rfl
  have hdiff :
      resolvent a z - resolvent a ζ =
        (ζ - z) • (resolvent a z * resolvent a ζ) := by
    rw [hresz, hresζ]
    calc
      Ring.inverse x - Ring.inverse y =
          Ring.inverse x * (y * Ring.inverse y) -
            (Ring.inverse x * x) * Ring.inverse y := by
        rw [Ring.mul_inverse_cancel y hy, Ring.inverse_mul_cancel x hx,
          mul_one, one_mul]
      _ = Ring.inverse x * (y - x) * Ring.inverse y := by noncomm_ring
      _ = Ring.inverse x * algebraMap ℂ A (ζ - z) * Ring.inverse y := by
        congr 2
        simp [x, y, map_sub]
      _ = algebraMap ℂ A (ζ - z) *
          (Ring.inverse x * Ring.inverse y) := by
        rw [(Algebra.commutes (ζ - z) (Ring.inverse x)).symm, mul_assoc]
      _ = (ζ - z) • (Ring.inverse x * Ring.inverse y) := by
        rw [Algebra.smul_def]
  have hζz : ζ - z ≠ 0 := sub_ne_zero.mpr hzζ.symm
  rw [hdiff, smul_smul, inv_mul_cancel₀ hζz, one_smul]

/-- **Riesz integral on the zero cycle.** Let `A` be a complete unital complex normed algebra
with its given norm and `a∈A`. Write `R_Γ(a,f)=(2πi)⁻¹ • ∮_Γ f(z) • (z·1-a)⁻¹ dz`, with
total inverse. For every scalar function `f`, `R_0(a,f)=0`. There is no regularity premise
on `f` and the algebra may be zero. -/
@[simp]
theorem rieszIntegral_zero (a : A) (f : ℂ → ℂ) :
    rieszIntegral (0 : RectilinearCycle) a f = 0 := by
  simp [rieszIntegral]

/-- **Differentiability of the Riesz integrand off the spectrum.** Let `A` be a complete
unital complex normed algebra with its given norm and `a∈A`. If `f:ℂ→ℂ` is complex
differentiable on `G⊆ℂ`, then `z↦f(z) • (z·1-a)⁻¹` is complex differentiable on
`G∖spectrum ℂ a`. Neither openness of `G` nor a nonzero algebra is an additional premise. -/
theorem differentiableOn_rieszIntegrand {a : A} {f : ℂ → ℂ} {G : Set ℂ}
    (hf : DifferentiableOn ℂ f G) :
    DifferentiableOn ℂ (rieszIntegrand a f) (G \ spectrum ℂ a) := by
  intro z hz
  have hzres : z ∈ resolventSet ℂ a := by
    exact spectrum.mem_resolventSet_iff.mpr (spectrum.notMem_iff.mp hz.2)
  exact (hf.mono sdiff_subset z hz).smul
    (spectrum.hasDerivAt_resolvent_const_left hzres).differentiableAt.differentiableWithinAt

/-- **Riesz integral invariance under rectangular homology.** Let `A` be a complete unital
complex normed algebra with its given norm and `a∈A`. Write `R_Γ(a,f)=(2πi)⁻¹ • ∮_Γ f(z) •
(z·1-a)⁻¹ dz`, with total inverse. Let `f` be complex differentiable on `G⊆ℂ`. If every
rectangle with nonzero coefficient in `Γ-Λ` has its closed carrier contained in
`G∖spectrum ℂ a`, so that the cycles are homologous there, then `R_Γ(a,f)=R_Λ(a,f)`. The
homology relation is the finite rectangular filling relation. -/
theorem rieszIntegral_eq_of_homologousIn {Γ Λ : RectilinearCycle} {a : A}
    {f : ℂ → ℂ} {G : Set ℂ} (hΓΛ : Γ.HomologousIn Λ (G \ spectrum ℂ a))
    (hf : DifferentiableOn ℂ f G) :
    rieszIntegral Γ a f = rieszIntegral Λ a f := by
  apply congrArg (((2 * Real.pi : ℂ) * Complex.I)⁻¹ • ·)
  exact Γ.integral_eq_of_homologousIn hΓΛ (differentiableOn_rieszIntegrand hf)

/-- **Contour independence for admissible spectrum grids.** Let `A` be a complete unital
complex normed algebra with its given norm and `a∈A`. Write `R_Γ(a,f)=(2πi)⁻¹ • ∮_Γ f(z) •
(z·1-a)⁻¹ dz`, with total inverse. A filling is admissible for `S=spectrum ℂ a` in `G⊆ℂ`
when its reduced trace lies in `G∖S`, its cycle index is one on `S`, and its index is zero
outside `G`. If `D` and `H` are both admissible for `S` in `G` and `f` is complex
differentiable on `G`, then `R_{D.toCycle}(a,f)=R_{H.toCycle}(a,f)`. Filled-region
containment in `G` is not part of the admissibility predicate. -/
theorem rieszIntegral_eq_of_isAdmissibleFor {D E : GridFilling} {a : A}
    {f : ℂ → ℂ} {G : Set ℂ}
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G)
    (hE : E.IsAdmissibleFor (spectrum ℂ a) G)
    (hf : DifferentiableOn ℂ f G) :
    rieszIntegral D.toCycle a f = rieszIntegral E.toCycle a f := by
  apply congrArg (((2 * Real.pi : ℂ) * Complex.I)⁻¹ • ·)
  exact GridFilling.integral_eq_of_isAdmissibleFor hD hE
    (differentiableOn_rieszIntegrand hf)

/-- **The constant-one Riesz value on a spectrum contour.** Let `A` be a complete unital
complex normed algebra with its given norm and `a∈A`. Write `R_Γ(a,f)=(2πi)⁻¹ • ∮_Γ f(z) •
(z·1-a)⁻¹ dz`, with total inverse. A filling is admissible for `S=spectrum ℂ a` in `G⊆ℂ`
when its reduced trace lies in `G∖S`, its cycle index is one on `S`, and its index is zero
outside `G`. For every admissible `D`, `R_{D.toCycle}(a,z↦1)=1_A`. No openness assumption
on `G` is needed; the zero algebra is included. -/
theorem rieszIntegral_one_of_isAdmissibleFor
    {D : GridFilling} {a : A} {G : Set ℂ}
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszIntegral D.toCycle a (fun _ : ℂ ↦ 1) = 1 := by
  classical
  let R : ℝ := 2 * (‖a‖ + ‖a‖ * ‖(1 : A)‖ + 1)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have haR : 2 * ‖a‖ < R := by
    dsimp [R]
    nlinarith [norm_nonneg (1 : A)]
  have hσR : ‖a‖ * ‖(1 : A)‖ < R := by
    dsimp [R]
    nlinarith [norm_nonneg a, norm_nonneg (1 : A)]
  let q : ℝ := ‖a‖ / R
  have hq₀ : 0 ≤ q := div_nonneg (norm_nonneg a) hR.le
  have hqhalf : q < (2 : ℝ)⁻¹ := by
    rw [show q = ‖a‖ / R by rfl, div_lt_iff₀ hR]
    nlinarith
  have hq₁ : q < 1 := hqhalf.trans (by norm_num)
  let K : Set ℂ := Metric.closedBall 0 R
  obtain ⟨E, hE⟩ := GridFilling.exists_isAdmissibleFor
    (isCompact_closedBall (0 : ℂ) R) isOpen_univ (subset_univ K)
  have hσK : spectrum ℂ a ⊆ K := by
    dsimp [K]
    exact (spectrum.subset_closedBall_norm_mul a).trans
      (Metric.closedBall_subset_closedBall hσR.le)
  have hEσ : E.IsAdmissibleFor (spectrum ℂ a) Set.univ := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact ⟨mem_univ z, fun hzσ ↦ (hE.1 hz).2 (hσK hzσ)⟩
    · intro z hzσ
      exact hE.2.1 z (hσK hzσ)
    · intro z hz
      exact (hz (mem_univ z)).elim
  have hzeroK : (0 : ℂ) ∈ K := by
    simp [K, hR.le]
  have hzeroTrace : (0 : ℂ) ∉ E.reducedTrace := fun hz ↦
    (hE.1 hz).2 hzeroK
  have htraceNorm (z : ℂ) (hz : z ∈ E.reducedTrace) : R < ‖z‖ := by
    have hzK := (hE.1 hz).2
    simpa [K, Metric.mem_closedBall, dist_zero_right] using hzK
  have hz_ne (z : ℂ) (hz : z ∈ E.reducedTrace) : z ≠ 0 := by
    exact norm_pos_iff.mp (hR.trans (htraceNorm z hz))
  have ht_le_q (z : ℂ) (hz : z ∈ E.reducedTrace) :
      ‖z⁻¹ • a‖ ≤ q := by
    calc
      ‖z⁻¹ • a‖ = ‖a‖ / ‖z‖ := by
        rw [norm_smul, norm_inv, div_eq_mul_inv, mul_comm]
      _ ≤ ‖a‖ / R :=
        div_le_div_of_nonneg_left (norm_nonneg a) hR (htraceNorm z hz).le
      _ = q := rfl
  have hzpowCont (m : ℤ) :
      ContinuousOn (fun z : ℂ ↦ z ^ m) E.reducedTrace :=
    (continuousOn_zpow₀ m).mono fun z hz ↦ by
      simpa only [mem_compl_iff, mem_singleton_iff] using hz_ne z hz
  have hresCont : ContinuousOn (resolvent a) E.reducedTrace := by
    intro z hz
    have hzres : z ∈ resolventSet ℂ a := by
      exact spectrum.notMem_iff.mp (hEσ.1 hz).2
    exact (spectrum.hasDerivAt_resolvent_const_left hzres).continuousAt.continuousWithinAt
  have hinvCont : ContinuousOn (fun z : ℂ ↦ z⁻¹) E.reducedTrace :=
    continuousOn_inv₀.mono fun z hz ↦ by
      simpa only [mem_compl_iff, mem_singleton_iff] using hz_ne z hz
  have htCont : ContinuousOn (fun z : ℂ ↦ z⁻¹ • a) E.reducedTrace :=
    hinvCont.smul continuousOn_const
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast Real.two_pi_pos.ne') Complex.I_ne_zero
  have hinvIntegral : E.toCycle.integral (fun z : ℂ ↦ z⁻¹) = c := by
    simpa [c] using toCycle_integral_inv_eq_two_pi_I E hE hzeroK
  have htermCont (n : ℕ) : ContinuousOn
      (fun z : ℂ ↦ z ^ (Int.negSucc n) • a ^ n) E.reducedTrace :=
    (hzpowCont (Int.negSucc n)).smul continuousOn_const
  have htermIntegral (n : ℕ) :
      E.toCycle.integral (fun z : ℂ ↦ z ^ (Int.negSucc n) • a ^ n) =
        if n = 0 then c • (1 : A) else 0 := by
    have hspan := toCycle_integral_smul_const E
      (fun z : ℂ ↦ z ^ (Int.negSucc n)) (a ^ n)
      (hzpowCont (Int.negSucc n))
    by_cases hn : n = 0
    · subst n
      simpa [hinvIntegral] using hspan
    · have hm : Int.negSucc n ≠ -1 := by omega
      have hzint := GridFilling.toCycle_integral_zpow_eq_zero E hm hzeroTrace
      calc
        E.toCycle.integral (fun z : ℂ ↦ z ^ (Int.negSucc n) • a ^ n) =
            E.toCycle.integral (fun z : ℂ ↦ z ^ (Int.negSucc n)) • a ^ n := hspan
        _ = 0 := by rw [hzint, zero_smul]
        _ = if n = 0 then c • (1 : A) else 0 := by simp [hn]
  have hpolyCont (N : ℕ) : ContinuousOn
      (fun z : ℂ ↦ ∑ n ∈ Finset.range (N + 1),
        z ^ (Int.negSucc n) • a ^ n) E.reducedTrace :=
    continuousOn_finsetSum _ fun n hn ↦ htermCont n
  have hpolyIntegral (N : ℕ) :
      E.toCycle.integral (fun z : ℂ ↦ ∑ n ∈ Finset.range (N + 1),
        z ^ (Int.negSucc n) • a ^ n) = c • (1 : A) := by
    rw [toCycle_integral_finsetSum E]
    · rw [Finset.sum_eq_single 0]
      · simpa using htermIntegral 0
      · intro n hn hne
        simpa [hne] using htermIntegral n
      · simp
    · intro n hn
      exact htermCont n
  let rem : ℕ → ℂ → A := fun N z ↦
    (z⁻¹ • a) ^ (N + 1) * resolvent a z
  have hremCont (N : ℕ) : ContinuousOn (rem N) E.reducedTrace := by
    dsimp [rem]
    exact (htCont.pow (N + 1)).mul hresCont
  have hexpand (N : ℕ) :
      E.toCycle.integral (resolvent a) =
        c • (1 : A) + E.toCycle.integral (rem N) := by
    calc
      E.toCycle.integral (resolvent a) =
          E.toCycle.integral (fun z ↦
            (∑ n ∈ Finset.range (N + 1), z ^ (Int.negSucc n) • a ^ n) +
              rem N z) := by
        rw [E.toCycle_integral_eq_reducedIntegral,
          E.toCycle_integral_eq_reducedIntegral]
        apply E.reducedIntegral_congr
        intro z hz
        simpa [rem] using resolvent_eq_finsetSum_zpow_add_remainder
          a z (hz_ne z hz) (N + 1) ((ht_le_q z hz).trans_lt hq₁)
      _ = E.toCycle.integral (fun z ↦
            ∑ n ∈ Finset.range (N + 1), z ^ (Int.negSucc n) • a ^ n) +
          E.toCycle.integral (rem N) :=
        E.toCycle_integral_add (hpolyCont N) (hremCont N)
      _ = c • (1 : A) + E.toCycle.integral (rem N) := by
        rw [hpolyIntegral]
  let B : ℝ := ‖(1 : A)‖ + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hresBound (z : ℂ) (hz : z ∈ E.reducedTrace) :
      ‖resolvent a z‖ ≤ R⁻¹ * B := by
    calc
      ‖resolvent a z‖ ≤ ‖z‖⁻¹ * (‖(1 : A)‖ + 1) :=
        norm_resolvent_le_of_two_mul_norm_lt a z
          (haR.trans (htraceNorm z hz))
      _ ≤ R⁻¹ * (‖(1 : A)‖ + 1) := by
        gcongr
        exact (htraceNorm z hz).le
      _ = R⁻¹ * B := rfl
  have hremBound (N : ℕ) (z : ℂ) (hz : z ∈ E.reducedTrace) :
      ‖rem N z‖ ≤ q ^ (N + 1) * (R⁻¹ * B) := by
    dsimp [rem]
    calc
      ‖(z⁻¹ • a) ^ (N + 1) * resolvent a z‖ ≤
          ‖(z⁻¹ • a) ^ (N + 1)‖ * ‖resolvent a z‖ := norm_mul_le _ _
      _ ≤ ‖z⁻¹ • a‖ ^ (N + 1) * ‖resolvent a z‖ := by
        gcongr
        exact norm_pow_le' _ (Nat.succ_pos N)
      _ ≤ q ^ (N + 1) * (R⁻¹ * B) := by
        exact mul_le_mul
          (pow_le_pow_left₀ (norm_nonneg _) (ht_le_q z hz) (N + 1))
          (hresBound z hz) (norm_nonneg _)
          (pow_nonneg hq₀ (N + 1))
  let L : ℝ := (E.boundaryEdges.card : ℝ) / E.scale
  have hremIntegralBound (N : ℕ) :
      ‖E.toCycle.integral (rem N)‖ ≤
        L * (q ^ (N + 1) * (R⁻¹ * B)) := by
    exact E.norm_toCycle_integral_le_of_norm_le (hremBound N)
  have hpow : Tendsto (fun N : ℕ ↦ q ^ (N + 1)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).comp
      (tendsto_add_atTop_nat 1)
  have hmajor : Tendsto
      (fun N : ℕ ↦ L * (q ^ (N + 1) * (R⁻¹ * B))) atTop (nhds 0) := by
    simpa using (hpow.mul_const (R⁻¹ * B)).const_mul L
  have hremZero : Tendsto (fun N : ℕ ↦ E.toCycle.integral (rem N))
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun N ↦ norm_nonneg _) hremIntegralBound hmajor
  have hconst : E.toCycle.integral (resolvent a) = c • (1 : A) := by
    have htendSum : Tendsto
        (fun N : ℕ ↦ c • (1 : A) + E.toCycle.integral (rem N))
        atTop (nhds (c • (1 : A))) := by
      simpa using tendsto_const_nhds.add hremZero
    have htend : Tendsto (fun _ : ℕ ↦ E.toCycle.integral (resolvent a))
        atTop (nhds (c • (1 : A))) :=
      Filter.Tendsto.congr'
        (Eventually.of_forall fun N ↦ (hexpand N).symm) htendSum
    exact (tendsto_nhds_unique htend tendsto_const_nhds).symm
  have hEvalE : rieszIntegral E.toCycle a (fun _ : ℂ ↦ 1) = 1 := by
    rw [rieszIntegral]
    change c⁻¹ • E.toCycle.integral
      (rieszIntegrand a (fun _ : ℂ ↦ 1)) = 1
    rw [show rieszIntegrand a (fun _ : ℂ ↦ 1) = resolvent a by
      funext z
      simp [rieszIntegrand]]
    rw [hconst]
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  calc
    rieszIntegral D.toCycle a (fun _ : ℂ ↦ 1) =
        rieszIntegral E.toCycle a (fun _ : ℂ ↦ 1) :=
      rieszIntegral_eq_of_isAdmissibleFor
        (hD.mono_right (subset_univ _)) hEσ
          (differentiableOn_const (1 : ℂ))
    _ = 1 := hEvalE

/-- **The coordinate Riesz value on a spectrum contour.** Let `A` be a complete unital complex
normed algebra with its given norm and `a∈A`. Write `R_Γ(a,f)=(2πi)⁻¹ • ∮_Γ f(z) •
(z·1-a)⁻¹ dz`, with total inverse. A filling is admissible for `S=spectrum ℂ a` in `G⊆ℂ`
when its reduced trace lies in `G∖S`, its cycle index is one on `S`, and its index is zero
outside `G`. For every admissible `D`, `R_{D.toCycle}(a,z↦z)=a`. No openness assumption on
`G` is needed, and the formula includes the zero algebra. -/
theorem rieszIntegral_id_of_isAdmissibleFor
    {D : GridFilling} {a : A} {G : Set ℂ}
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszIntegral D.toCycle a id = a := by
  have hresCont : ContinuousOn (resolvent a) D.reducedTrace := by
    intro z hz
    have hzres : z ∈ resolventSet ℂ a :=
      spectrum.notMem_iff.mp (hD.1 hz).2
    exact
      (spectrum.hasDerivAt_resolvent_const_left hzres).continuousAt.continuousWithinAt
  have hpoint (z : ℂ) (hz : z ∈ D.reducedTrace) :
      z • resolvent a z = 1 + a * resolvent a z := by
    have hzres : z ∈ resolventSet ℂ a :=
      spectrum.notMem_iff.mp (hD.1 hz).2
    have hresolvent :
        (algebraMap ℂ A z - a) * resolvent a z = 1 := by
      calc
        (algebraMap ℂ A z - a) * resolvent a z =
            (algebraMap ℂ A z - a) * (↑hzres.unit⁻¹ : A) := by
          rw [spectrum.resolvent_eq hzres]
        _ = (↑hzres.unit : A) * (↑hzres.unit⁻¹ : A) :=
          congrArg (fun w : A ↦ w * (↑hzres.unit⁻¹ : A)) hzres.unit_spec.symm
        _ = 1 := hzres.unit.mul_inv
    apply sub_eq_iff_eq_add.mp
    calc
      z • resolvent a z - a * resolvent a z =
          (z • (1 : A) - a) * resolvent a z := by
        rw [sub_mul, smul_mul_assoc, one_mul]
      _ = (algebraMap ℂ A z - a) * resolvent a z := by
        rw [Algebra.algebraMap_eq_smul_one]
      _ = 1 := hresolvent
  have honeIntegral :
      D.toCycle.integral (fun _ : ℂ ↦ (1 : A)) = 0 := by
    apply D.toCycle_integral_eq_zero_of_hasDerivAt
      (F := fun z : ℂ ↦ z • (1 : A)) continuousOn_const
    intro z hz
    simpa using (hasDerivAt_id (x := z)).smul_const (1 : A)
  have hmulIntegral :
      D.toCycle.integral (fun z ↦ a * resolvent a z) =
        a * D.toCycle.integral (resolvent a) := by
    rw [D.toCycle_integral_eq_reducedIntegral,
      D.toCycle_integral_eq_reducedIntegral]
    let L : A →L[ℂ] A := ContinuousLinearMap.mulLeftRight ℂ A a 1
    have hL := D.reducedIntegral_comp_comm L (resolvent a)
      (fun _ hz ↦ hz) hresCont
    simpa [L] using hL
  have hcoordinateIntegral :
      D.toCycle.integral (fun z ↦ z • resolvent a z) =
        D.toCycle.integral (fun _ : ℂ ↦ (1 : A)) +
          D.toCycle.integral (fun z ↦ a * resolvent a z) := by
    calc
      D.toCycle.integral (fun z ↦ z • resolvent a z) =
          D.toCycle.integral (fun z ↦ (1 : A) + a * resolvent a z) := by
        rw [D.toCycle_integral_eq_reducedIntegral,
          D.toCycle_integral_eq_reducedIntegral]
        apply D.reducedIntegral_congr
        intro z hz
        exact hpoint z hz
      _ = D.toCycle.integral (fun _ : ℂ ↦ (1 : A)) +
          D.toCycle.integral (fun z ↦ a * resolvent a z) := by
        have hmulCont : ContinuousOn (fun z ↦ a * resolvent a z)
            D.reducedTrace :=
          (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ a) D.reducedTrace).mul
            hresCont
        have hadd := D.toCycle_integral_add
          (f := fun _ : ℂ ↦ (1 : A))
          (g := fun z ↦ a * resolvent a z)
          (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : A)) D.reducedTrace)
          hmulCont
        change D.toCycle.integral (fun z ↦ (1 : A) + a * resolvent a z) =
          D.toCycle.integral (fun _ : ℂ ↦ (1 : A)) +
            D.toCycle.integral (fun z ↦ a * resolvent a z) at hadd
        exact hadd
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have honeNormalized :
      c⁻¹ • D.toCycle.integral (resolvent a) = 1 := by
    have hone := rieszIntegral_one_of_isAdmissibleFor hD
    rw [rieszIntegral] at hone
    change c⁻¹ • D.toCycle.integral
      (rieszIntegrand a (fun _ : ℂ ↦ 1)) = 1 at hone
    rw [show rieszIntegrand a (fun _ : ℂ ↦ 1) = resolvent a by
      funext z
      simp [rieszIntegrand]] at hone
    exact hone
  rw [rieszIntegral]
  change c⁻¹ • D.toCycle.integral (fun z ↦ z • resolvent a z) = a
  rw [hcoordinateIntegral, honeIntegral, zero_add, hmulIntegral]
  calc
    c⁻¹ • (a * D.toCycle.integral (resolvent a)) =
        a * (c⁻¹ • D.toCycle.integral (resolvent a)) :=
      (Algebra.mul_smul_comm _ _ _).symm
    _ = a := by rw [honeNormalized, mul_one]

/-- **Riesz integral depends on scalar values on the reduced trace.** Let `A` be a complete
unital complex normed algebra with its given norm and `a∈A`. Write `R_Γ(a,f)=(2πi)⁻¹ • ∮_Γ
f(z) • (z·1-a)⁻¹ dz`, with total inverse. Let `D` be a positive-scale finite grid filling
and `f,g:ℂ→ℂ` agree on its reduced trace. Then `R_{D.toCycle}(a,f)=R_{D.toCycle}(a,g)`. No
continuity, differentiability, or admissibility premise is required. -/
theorem rieszIntegral_congr_of_eqOn_reducedTrace (D : GridFilling) (a : A)
    {f g : ℂ → ℂ} (hfg : Set.EqOn f g D.reducedTrace) :
    rieszIntegral D.toCycle a f = rieszIntegral D.toCycle a g := by
  apply congrArg (((2 * Real.pi : ℂ) * Complex.I)⁻¹ • ·)
  rw [D.toCycle_integral_eq_reducedIntegral,
    D.toCycle_integral_eq_reducedIntegral]
  apply D.reducedIntegral_congr
  intro z hz
  simp [rieszIntegrand, hfg hz]
