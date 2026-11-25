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

public import MathlibExt.Analysis.Normed.Algebra.RieszIntegral
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.NhdsSet
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Holomorphic germs and the Riesz algebra homomorphism

For an element `a` of a unital complex normed algebra, `SpectrumGerm a` is
the ring of scalar-function germs at the neighborhood filter of its complex
spectrum. Two representatives have the same germ when they agree on some
neighborhood of that spectrum. Holomorphic germs are those represented by a
function analytic near every spectral point. They form a complex algebra,
with scalar constants and the coordinate germ `z ↦ z`. These germ and
representative constructions require no completeness or nonzero-algebra
hypothesis.

A representative is analytic on an open set containing the spectrum. Scalar
power series define such germs when their convergence radius strictly exceeds
the spectral radius of `a`; values of their sums outside the convergence disk
do not change the germ. At a spectral point `z₀`, subtracting the value gives
a factorization by the coordinate germ minus `z₀`. If a germ avoids a scalar
value on the spectrum, subtracting that scalar yields a unit of the germ
algebra.

When the algebra is complete, integration around an admissible finite grid
contour defines the Riesz value `f(a)`. Its value is independent of the
representative and admissible grid. It preserves addition, ordered
multiplication and complex scalar multiplication, sends the constant-one germ
to `1`, and sends the coordinate germ to `a`. The resulting map is a complex
algebra homomorphism into the original, possibly noncommutative algebra.
The zero algebra and empty spectrum retain the same total definitions.
-/

@[expose] public section


open Filter Set
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Germs of scalar functions on neighborhoods of the spectrum of `a`.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
abbrev SpectrumGerm (a : A) := Filter.Germ (𝓝ˢ (spectrum ℂ a)) ℂ

/-- A spectrum germ is holomorphic when one (equivalently every)
representative is analytic on a neighborhood of every spectral point.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
def IsHolomorphicNearSpectrum (a : A) (f : SpectrumGerm a) : Prop :=
  f.liftOn (fun F ↦ AnalyticOnNhd ℂ F (spectrum ℂ a)) fun F G hFG ↦ by
    apply propext
    constructor
    · intro hF z hz
      exact (hF z hz).congr (hFG.filter_mono (nhds_le_nhdsSet hz))
    · intro hG z hz
      exact (hG z hz).congr (hFG.symm.filter_mono (nhds_le_nhdsSet hz))

/-- A global scalar function determines a holomorphic spectrum germ exactly when it is analytic on
a neighborhood of every spectral point.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem isHolomorphicNearSpectrum_coe (a : A) (f : ℂ → ℂ) :
    IsHolomorphicNearSpectrum a (f : SpectrumGerm a) ↔
      AnalyticOnNhd ℂ f (spectrum ℂ a)
``` -/
@[simp]
theorem isHolomorphicNearSpectrum_coe (a : A) (f : ℂ → ℂ) :
    IsHolomorphicNearSpectrum a (f : SpectrumGerm a) ↔
      AnalyticOnNhd ℂ f (spectrum ℂ a) :=
  Iff.rfl

/-- The zero spectrum germ is holomorphic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.zero (a : A) :
    IsHolomorphicNearSpectrum a 0
``` -/
theorem IsHolomorphicNearSpectrum.zero (a : A) :
    IsHolomorphicNearSpectrum a 0 :=
  analyticOnNhd_const

/-- The constant-one spectrum germ is holomorphic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.one (a : A) :
    IsHolomorphicNearSpectrum a 1
``` -/
theorem IsHolomorphicNearSpectrum.one (a : A) :
    IsHolomorphicNearSpectrum a 1 :=
  analyticOnNhd_const

/-- The sum of two holomorphic spectrum germs is holomorphic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.add (a : A) {f g : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f)
    (hg : IsHolomorphicNearSpectrum a g) :
    IsHolomorphicNearSpectrum a (f + g)
``` -/
theorem IsHolomorphicNearSpectrum.add (a : A) {f g : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f)
    (hg : IsHolomorphicNearSpectrum a g) :
    IsHolomorphicNearSpectrum a (f + g) := by
  refine Filter.Germ.inductionOn₂ f g ?_ hf hg
  intro F G hF hG
  exact AnalyticOnNhd.add hF hG

/-- The additive inverse of a holomorphic spectrum germ is holomorphic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.neg (a : A) {f : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f) :
    IsHolomorphicNearSpectrum a (-f)
``` -/
theorem IsHolomorphicNearSpectrum.neg (a : A) {f : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f) :
    IsHolomorphicNearSpectrum a (-f) := by
  refine Filter.Germ.inductionOn f ?_ hf
  intro F hF
  exact AnalyticOnNhd.neg hF

/-- The product of two holomorphic spectrum germs is holomorphic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.mul (a : A) {f g : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f)
    (hg : IsHolomorphicNearSpectrum a g) :
    IsHolomorphicNearSpectrum a (f * g)
``` -/
theorem IsHolomorphicNearSpectrum.mul (a : A) {f g : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f)
    (hg : IsHolomorphicNearSpectrum a g) :
    IsHolomorphicNearSpectrum a (f * g) := by
  refine Filter.Germ.inductionOn₂ f g ?_ hf hg
  intro F G hF hG
  exact AnalyticOnNhd.mul hF hG

/-- Complex scalar multiplication preserves holomorphic spectrum germs.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.const_smul (a : A) (c : ℂ)
    {f : SpectrumGerm a} (hf : IsHolomorphicNearSpectrum a f) :
    IsHolomorphicNearSpectrum a (c • f)
``` -/
theorem IsHolomorphicNearSpectrum.const_smul (a : A) (c : ℂ)
    {f : SpectrumGerm a} (hf : IsHolomorphicNearSpectrum a f) :
    IsHolomorphicNearSpectrum a (c • f) := by
  refine Filter.Germ.inductionOn f ?_ hf
  intro F hF
  exact AnalyticOnNhd.const_smul (c := c) hF

/-- The subring of spectrum germs represented by scalar functions analytic near the spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable def holomorphicNearSpectrumSubring (a : A) :
    Subring (SpectrumGerm a) where
  carrier := {f | IsHolomorphicNearSpectrum a f}
  zero_mem' := IsHolomorphicNearSpectrum.zero a
  one_mem' := IsHolomorphicNearSpectrum.one a
  add_mem' := IsHolomorphicNearSpectrum.add a
  neg_mem' := IsHolomorphicNearSpectrum.neg a
  mul_mem' := IsHolomorphicNearSpectrum.mul a

/-- The complex algebra of holomorphic scalar-function germs near the spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
abbrev HolomorphicNearSpectrum (a : A) := ↥(holomorphicNearSpectrumSubring a)

/-- A globally defined function analytic near the spectrum determines an
element of `Hol(a)`.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable def HolomorphicNearSpectrum.ofFunction (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) : HolomorphicNearSpectrum a :=
  ⟨(f : SpectrumGerm a), hf⟩

/-- Two analytic scalar representatives define the same holomorphic germ exactly when they agree on
a neighborhood of the spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.ofFunction_eq_iff_eventuallyEq (a : A)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a))
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a f hf =
        HolomorphicNearSpectrum.ofFunction a g hg ↔
      f =ᶠ[𝓝ˢ (spectrum ℂ a)] g
``` -/
theorem HolomorphicNearSpectrum.ofFunction_eq_iff_eventuallyEq (a : A)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a))
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a f hf =
        HolomorphicNearSpectrum.ofFunction a g hg ↔
      f =ᶠ[𝓝ˢ (spectrum ℂ a)] g := by
  constructor
  · intro h
    exact Filter.Germ.coe_eq.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Filter.Germ.coe_eq.mpr h)

/-- Constant holomorphic germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable def HolomorphicNearSpectrum.const (a : A) (c : ℂ) :
    HolomorphicNearSpectrum a :=
  .ofFunction a (fun _ ↦ c) analyticOnNhd_const

/-- The coordinate germ `z ↦ z`.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable def HolomorphicNearSpectrum.coordinate (a : A) :
    HolomorphicNearSpectrum a :=
  .ofFunction a id analyticOnNhd_id

/-- The scalar algebra structure on the classical `Hol(a)`.  Scalar constants are
represented by constant germs; no star operation is asserted.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable instance HolomorphicNearSpectrum.instAlgebra (a : A) :
    Algebra ℂ (HolomorphicNearSpectrum a) where
  smul c f :=
    ⟨c • (f : SpectrumGerm a),
      IsHolomorphicNearSpectrum.const_smul a c f.property⟩
  algebraMap :=
    { toFun := HolomorphicNearSpectrum.const a
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' c d := by
        apply Subtype.ext
        rfl
      map_zero' := by
        apply Subtype.ext
        rfl
      map_add' c d := by
        apply Subtype.ext
        rfl }
  commutes' c f := Subtype.ext (mul_comm _ _)
  smul_def' c f := by
    apply Subtype.ext
    exact Filter.Germ.inductionOn f.1 fun F ↦ rfl

/-- The scalar algebra map into holomorphic spectrum germs is the constant-germ map.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.algebraMap_apply (a : A) (c : ℂ) :
    algebraMap ℂ (HolomorphicNearSpectrum a) c =
      HolomorphicNearSpectrum.const a c
``` -/
@[simp]
theorem HolomorphicNearSpectrum.algebraMap_apply (a : A) (c : ℂ) :
    algebraMap ℂ (HolomorphicNearSpectrum a) c =
      HolomorphicNearSpectrum.const a c :=
  rfl

/-- The underlying spectrum germ of a scalar multiple is the scalar multiple of the underlying germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.coe_smul (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    ((c • f : HolomorphicNearSpectrum a) : SpectrumGerm a) = c • f.1
``` -/
@[simp]
theorem HolomorphicNearSpectrum.coe_smul (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    ((c • f : HolomorphicNearSpectrum a) : SpectrumGerm a) = c • f.1 :=
  rfl

/-- Taking an analytic representative to its spectrum germ preserves addition.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.ofFunction_add (a : A)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a))
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a (f + g) (hf.add hg) =
      HolomorphicNearSpectrum.ofFunction a f hf +
        HolomorphicNearSpectrum.ofFunction a g hg
``` -/
@[simp]
theorem HolomorphicNearSpectrum.ofFunction_add (a : A)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a))
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a (f + g) (hf.add hg) =
      HolomorphicNearSpectrum.ofFunction a f hf +
        HolomorphicNearSpectrum.ofFunction a g hg := by
  apply Subtype.ext
  rfl

/-- Taking an analytic representative to its spectrum germ preserves complex scalar multiplication.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.ofFunction_const_smul (a : A) (c : ℂ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a (c • f) hf.const_smul =
      c • HolomorphicNearSpectrum.ofFunction a f hf
``` -/
@[simp]
theorem HolomorphicNearSpectrum.ofFunction_const_smul (a : A) (c : ℂ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a (c • f) hf.const_smul =
      c • HolomorphicNearSpectrum.ofFunction a f hf := by
  apply Subtype.ext
  rfl

/-- A global scalar representative of the given holomorphic germ, analytic near the spectrum and
equal to that germ on a spectrum neighborhood.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable def HolomorphicNearSpectrum.rep (a : A)
    (f : HolomorphicNearSpectrum a) : ℂ → ℂ :=
  Quotient.out f.1

/-- The chosen representative has exactly the original spectrum germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_germ (a : A)
    (f : HolomorphicNearSpectrum a) :
    (f.rep a : SpectrumGerm a) = f.1
``` -/
theorem HolomorphicNearSpectrum.rep_germ (a : A)
    (f : HolomorphicNearSpectrum a) :
    (f.rep a : SpectrumGerm a) = f.1 :=
  Quotient.out_eq _

/-- Two holomorphic germs are equal exactly when their chosen representatives agree near the
spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.eq_iff_rep_eventuallyEq (a : A)
    (f g : HolomorphicNearSpectrum a) :
    f = g ↔ f.rep a =ᶠ[𝓝ˢ (spectrum ℂ a)] g.rep a
``` -/
theorem HolomorphicNearSpectrum.eq_iff_rep_eventuallyEq (a : A)
    (f g : HolomorphicNearSpectrum a) :
    f = g ↔ f.rep a =ᶠ[𝓝ˢ (spectrum ℂ a)] g.rep a := by
  constructor
  · rintro rfl
    exact Filter.EventuallyEq.rfl
  · intro h
    apply Subtype.ext
    rw [← f.rep_germ a, ← g.rep_germ a]
    exact Filter.Germ.coe_eq.mpr h

/-- The representative of a constant germ has the same germ as the corresponding constant function.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_const_germ (a : A) (c : ℂ) :
    ((HolomorphicNearSpectrum.const a c).rep a : SpectrumGerm a) =
      ((fun _ : ℂ ↦ c) : SpectrumGerm a)
``` -/
theorem HolomorphicNearSpectrum.rep_const_germ (a : A) (c : ℂ) :
    ((HolomorphicNearSpectrum.const a c).rep a : SpectrumGerm a) =
      ((fun _ : ℂ ↦ c) : SpectrumGerm a) := by
  rw [HolomorphicNearSpectrum.rep_germ]
  rfl

/-- The representative of the coordinate germ has the same germ as the identity scalar function.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_coordinate_germ (a : A) :
    ((HolomorphicNearSpectrum.coordinate a).rep a : SpectrumGerm a) =
      ((id : ℂ → ℂ) : SpectrumGerm a)
``` -/
theorem HolomorphicNearSpectrum.rep_coordinate_germ (a : A) :
    ((HolomorphicNearSpectrum.coordinate a).rep a : SpectrumGerm a) =
      ((id : ℂ → ℂ) : SpectrumGerm a) := by
  rw [HolomorphicNearSpectrum.rep_germ]
  rfl

/-- The representative of a sum has the sum of the two representative germs.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_add_germ (a : A)
    (f g : HolomorphicNearSpectrum a) :
    ((f + g).rep a : SpectrumGerm a) =
      (f.rep a : SpectrumGerm a) + (g.rep a : SpectrumGerm a)
``` -/
theorem HolomorphicNearSpectrum.rep_add_germ (a : A)
    (f g : HolomorphicNearSpectrum a) :
    ((f + g).rep a : SpectrumGerm a) =
      (f.rep a : SpectrumGerm a) + (g.rep a : SpectrumGerm a) := by
  rw [HolomorphicNearSpectrum.rep_germ, f.rep_germ, g.rep_germ]
  rfl

private theorem HolomorphicNearSpectrum.rep_mul_germ (a : A)
    (f g : HolomorphicNearSpectrum a) :
    ((f * g).rep a : SpectrumGerm a) =
      (f.rep a : SpectrumGerm a) * (g.rep a : SpectrumGerm a) := by
  rw [HolomorphicNearSpectrum.rep_germ, f.rep_germ, g.rep_germ]
  rfl

/-- The representative of a scalar multiple has the scalar multiple of the representative germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_const_smul_germ (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    ((c • f).rep a : SpectrumGerm a) =
      c • (f.rep a : SpectrumGerm a)
``` -/
theorem HolomorphicNearSpectrum.rep_const_smul_germ (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    ((c • f).rep a : SpectrumGerm a) =
      c • (f.rep a : SpectrumGerm a) := by
  rw [HolomorphicNearSpectrum.rep_germ, f.rep_germ]
  rfl

/-- The chosen representative is analytic on a neighborhood of every spectral point.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.analyticOnNhd_rep (a : A)
    (f : HolomorphicNearSpectrum a) :
    AnalyticOnNhd ℂ (f.rep a) (spectrum ℂ a)
``` -/
theorem HolomorphicNearSpectrum.analyticOnNhd_rep (a : A)
    (f : HolomorphicNearSpectrum a) :
    AnalyticOnNhd ℂ (f.rep a) (spectrum ℂ a) := by
  have hf := f.property
  rw [← f.rep_germ a] at hf
  exact hf

/-- The open set of complex points where the chosen representative is analytic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable def HolomorphicNearSpectrum.analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) : Set ℂ :=
  {z | AnalyticAt ℂ (f.rep a) z}

/-- The representative analytic domain is open.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.isOpen_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) : IsOpen (f.analyticDomain a)
``` -/
theorem HolomorphicNearSpectrum.isOpen_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) : IsOpen (f.analyticDomain a) :=
  isOpen_analyticAt ℂ (f.rep a)

/-- The representative analytic domain contains the complex spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.spectrum_subset_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) :
    spectrum ℂ a ⊆ f.analyticDomain a
``` -/
theorem HolomorphicNearSpectrum.spectrum_subset_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) :
    spectrum ℂ a ⊆ f.analyticDomain a :=
  f.analyticOnNhd_rep a

/-- The chosen representative is complex differentiable throughout its analytic domain.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.differentiableOn_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) :
    DifferentiableOn ℂ (f.rep a) (f.analyticDomain a)
``` -/
theorem HolomorphicNearSpectrum.differentiableOn_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) :
    DifferentiableOn ℂ (f.rep a) (f.analyticDomain a) := by
  intro z hz
  exact hz.differentiableAt.differentiableWithinAt

/-!
### Power-series germs
-/

/-- The holomorphic spectrum germ represented by the scalar power series
`sum n, c n * z ^ n` when its radius of convergence strictly exceeds the
spectral radius. Values of `FormalMultilinearSeries.sum` outside its
convergence disk do not affect this germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed. -/
noncomputable def HolomorphicNearSpectrum.ofScalars
    (a : A) (c : ℕ → ℂ)
    (h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    HolomorphicNearSpectrum a :=
  let p := FormalMultilinearSeries.ofScalars ℂ c
  HolomorphicNearSpectrum.ofFunction a p.sum <|
    p.analyticOnNhd.mono <|
      fun z hz ↦ by
        rw [mem_eball_zero_iff]
        have hzle : (‖z‖₊ : ENNReal) ≤ spectralRadius ℂ a := by
          rw [spectralRadius_eq_of_unital]
          exact le_iSup₂_of_le z hz (le_refl (‖z‖₊ : ENNReal))
        exact hzle.trans_lt h

/-- The chosen representative of a scalar-series germ agrees, as a germ,
with the sum of the corresponding formal multilinear series.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_ofScalars_germ
    (a : A) (c : ℕ → ℂ)
    (h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    ((HolomorphicNearSpectrum.ofScalars a c h).rep a : SpectrumGerm a) =
      ((FormalMultilinearSeries.ofScalars ℂ c).sum : SpectrumGerm a)
``` -/
theorem HolomorphicNearSpectrum.rep_ofScalars_germ
    (a : A) (c : ℕ → ℂ)
    (h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    ((HolomorphicNearSpectrum.ofScalars a c h).rep a : SpectrumGerm a) =
      ((FormalMultilinearSeries.ofScalars ℂ c).sum : SpectrumGerm a) := by
  rw [HolomorphicNearSpectrum.rep_germ]
  rfl

/-!
### Holomorphic factorization and reciprocals
-/

/-- An element of `Hol(a)` admits the linear factorization used in the classical
proof of the spectral mapping theorem at every spectral point.  The divided
difference is analytic even when the zero has higher multiplicity.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.exists_factor_sub_eval
    (a : A) (f : HolomorphicNearSpectrum a) {z₀ : ℂ}
    (hz₀ : z₀ ∈ spectrum ℂ a) :
    ∃ g : HolomorphicNearSpectrum a,
      f - algebraMap ℂ (HolomorphicNearSpectrum a) (f.rep a z₀) =
        (HolomorphicNearSpectrum.coordinate a -
          algebraMap ℂ (HolomorphicNearSpectrum a) z₀) * g
``` -/
theorem HolomorphicNearSpectrum.exists_factor_sub_eval
    (a : A) (f : HolomorphicNearSpectrum a) {z₀ : ℂ}
    (hz₀ : z₀ ∈ spectrum ℂ a) :
    ∃ g : HolomorphicNearSpectrum a,
      f - algebraMap ℂ (HolomorphicNearSpectrum a) (f.rep a z₀) =
        (HolomorphicNearSpectrum.coordinate a -
          algebraMap ℂ (HolomorphicNearSpectrum a) z₀) * g := by
  have hdslope :
      AnalyticOnNhd ℂ (dslope (f.rep a) z₀) (spectrum ℂ a) := by
    intro z hz
    by_cases hzz₀ : z = z₀
    · subst z
      rcases f.analyticOnNhd_rep a z₀ hz₀ with ⟨p, hp⟩
      exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    · rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [
        (f.analyticOnNhd_rep a z hz).eventually_analyticAt,
        eventually_ne_nhds hzz₀] with w hw hww₀
      exact (differentiableAt_dslope_of_ne hww₀).2 hw.differentiableAt
  let g : HolomorphicNearSpectrum a :=
    HolomorphicNearSpectrum.ofFunction a (dslope (f.rep a) z₀) hdslope
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change f.1 - ((fun _ : ℂ ↦ f.rep a z₀) : SpectrumGerm a) =
    (((id : ℂ → ℂ) : SpectrumGerm a) -
      ((fun _ : ℂ ↦ z₀) : SpectrumGerm a)) *
        ((dslope (f.rep a) z₀) : SpectrumGerm a)
  rw [← f.rep_germ a]
  change
    ((fun z : ℂ ↦ f.rep a z - f.rep a z₀) : SpectrumGerm a) =
      ((fun z : ℂ ↦ (z - z₀) * dslope (f.rep a) z₀ z) :
        SpectrumGerm a)
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    simpa [smul_eq_mul] using (sub_smul_dslope (f.rep a) z₀ z).symm

/-- If a holomorphic spectrum germ avoids a scalar value on the spectrum,
then subtracting that scalar gives a unit of `Hol(a)`.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.isUnit_sub_const_of_ne_on_spectrum
    (a : A) (f : HolomorphicNearSpectrum a) {c : ℂ}
    (hc : ∀ z ∈ spectrum ℂ a, f.rep a z ≠ c) :
    IsUnit (f - algebraMap ℂ (HolomorphicNearSpectrum a) c)
``` -/
theorem HolomorphicNearSpectrum.isUnit_sub_const_of_ne_on_spectrum
    (a : A) (f : HolomorphicNearSpectrum a) {c : ℂ}
    (hc : ∀ z ∈ spectrum ℂ a, f.rep a z ≠ c) :
    IsUnit (f - algebraMap ℂ (HolomorphicNearSpectrum a) c) := by
  let q : ℂ → ℂ := fun z ↦ (f.rep a z - c)⁻¹
  have hne (z : ℂ) (hz : z ∈ spectrum ℂ a) : f.rep a z - c ≠ 0 :=
    sub_ne_zero.mpr (hc z hz)
  have hq : AnalyticOnNhd ℂ q (spectrum ℂ a) := by
    dsimp [q]
    exact ((f.analyticOnNhd_rep a).sub analyticOnNhd_const).inv hne
  have hneEventually :
      ∀ᶠ z in 𝓝ˢ (spectrum ℂ a), f.rep a z - c ≠ 0 := by
    change {z : ℂ | f.rep a z - c ≠ 0} ∈ 𝓝ˢ (spectrum ℂ a)
    rw [mem_nhdsSet_iff_forall]
    intro z hz
    exact ((f.analyticOnNhd_rep a z hz).sub analyticAt_const).continuousAt.eventually_ne
      (hne z hz)
  let g : HolomorphicNearSpectrum a :=
    HolomorphicNearSpectrum.ofFunction a q hq
  apply isUnit_iff_exists.mpr
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    change (f.1 - ((fun _ : ℂ ↦ c) : SpectrumGerm a)) *
      (q : SpectrumGerm a) = 1
    rw [← f.rep_germ a]
    change
      ((fun z : ℂ ↦ (f.rep a z - c) * q z) : SpectrumGerm a) =
        ((fun _ : ℂ ↦ (1 : ℂ)) : SpectrumGerm a)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hneEventually] with z hz
    simp [q, hz]
  · apply Subtype.ext
    change (q : SpectrumGerm a) *
      (f.1 - ((fun _ : ℂ ↦ c) : SpectrumGerm a)) = 1
    rw [← f.rep_germ a]
    change
      ((fun z : ℂ ↦ q z * (f.rep a z - c)) : SpectrumGerm a) =
        ((fun _ : ℂ ↦ (1 : ℂ)) : SpectrumGerm a)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hneEventually] with z hz
    simp [q, hz]

variable [CompleteSpace A]

private theorem GridFilling.toCycle_integral_congr_reducedTrace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {f g : ℂ → E} (hfg : Set.EqOn f g D.reducedTrace) :
    D.toCycle.integral f = D.toCycle.integral g := by
  simpa only [D.toCycle_integral_eq_reducedIntegral] using
    D.reducedIntegral_congr hfg

private theorem GridFilling.toCycle_integral_comp_comm
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : GridFilling) (L : E →L[ℂ] F) (f : ℂ → E)
    (hf : ContinuousOn f D.reducedTrace) :
    D.toCycle.integral (fun z ↦ L (f z)) = L (D.toCycle.integral f) := by
  simp only [D.toCycle_integral_eq_reducedIntegral]
  exact D.reducedIntegral_comp_comm L f Subset.rfl hf

private theorem GridFilling.toCycle_integral_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {f g : ℂ → E}
    (hf : ContinuousOn f D.reducedTrace)
    (hg : ContinuousOn g D.reducedTrace) :
    D.toCycle.integral (fun z ↦ f z - g z) =
      D.toCycle.integral f - D.toCycle.integral g := by
  have hneg := D.toCycle_integral_smul (-1 : ℂ) g hg
  have hadd := D.toCycle_integral_add hf hg.neg
  change D.toCycle.integral (fun z ↦ f z + -g z) =
    D.toCycle.integral f + D.toCycle.integral (fun z ↦ -g z) at hadd
  change D.toCycle.integral (fun z ↦ (-1 : ℂ) • g z) =
    (-1 : ℂ) • D.toCycle.integral g at hneg
  have hneg' : D.toCycle.integral (fun z ↦ -g z) =
      -D.toCycle.integral g := by
    simpa only [neg_smul, one_smul] using hneg
  simpa [sub_eq_add_neg] using hadd.trans
    (congrArg (D.toCycle.integral f + ·) hneg')

/-- An admissible positive finite-grid contour around the spectrum inside the chosen representative
analytic domain.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed. -/
noncomputable def HolomorphicNearSpectrum.contour (a : A)
    (f : HolomorphicNearSpectrum a) : GridFilling :=
  Classical.choose <| GridFilling.exists_isAdmissibleFor
    (spectrum.isCompact a) (f.isOpen_analyticDomain a)
    (f.spectrum_subset_analyticDomain a)

/-- The chosen contour has reduced trace in the analytic domain outside the spectrum, index one on
the spectrum and index zero outside the domain.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem HolomorphicNearSpectrum.contour_isAdmissibleFor (a : A)
    (f : HolomorphicNearSpectrum a) :
    (f.contour a).IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a)
``` -/
theorem HolomorphicNearSpectrum.contour_isAdmissibleFor (a : A)
    (f : HolomorphicNearSpectrum a) :
    (f.contour a).IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a) :=
  Classical.choose_spec <| GridFilling.exists_isAdmissibleFor
    (spectrum.isCompact a) (f.isOpen_analyticDomain a)
    (f.spectrum_subset_analyticDomain a)

/-- The normalized Riesz contour value of the holomorphic germ, evaluated using an analytic
representative and admissible contour.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed. -/
noncomputable def rieszFunctionalCalculus (a : A)
    (f : HolomorphicNearSpectrum a) : A :=
  rieszIntegral (f.contour a).toCycle a (f.rep a)

/-- Every admissible grid in the chosen representative analytic domain gives the same
functional-calculus value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_eq_rieszIntegral_rep (a : A)
    (f : HolomorphicNearSpectrum a) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a)) :
    rieszFunctionalCalculus a f = rieszIntegral D.toCycle a (f.rep a)
``` -/
theorem rieszFunctionalCalculus_eq_rieszIntegral_rep (a : A)
    (f : HolomorphicNearSpectrum a) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a)) :
    rieszFunctionalCalculus a f = rieszIntegral D.toCycle a (f.rep a) := by
  exact rieszIntegral_eq_of_isAdmissibleFor
    (f.contour_isAdmissibleFor a) hD
    (f.differentiableOn_analyticDomain a)

omit [CompleteSpace A] in
/-- Every scalar representative of the given germ agrees with the chosen representative on some
open neighborhood of the spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.exists_open_eqOn_rep
    (a : A) (f : HolomorphicNearSpectrum a) (g : ℂ → ℂ)
    (hg : (g : SpectrumGerm a) = f.1) :
    ∃ U : Set ℂ, IsOpen U ∧ spectrum ℂ a ⊆ U ∧ Set.EqOn (f.rep a) g U
``` -/
theorem HolomorphicNearSpectrum.exists_open_eqOn_rep
    (a : A) (f : HolomorphicNearSpectrum a) (g : ℂ → ℂ)
    (hg : (g : SpectrumGerm a) = f.1) :
    ∃ U : Set ℂ, IsOpen U ∧ spectrum ℂ a ⊆ U ∧ Set.EqOn (f.rep a) g U := by
  have hEq : f.rep a =ᶠ[𝓝ˢ (spectrum ℂ a)] g :=
    Filter.Germ.coe_eq.1 ((f.rep_germ a).trans hg.symm)
  change {z | f.rep a z = g z} ∈ 𝓝ˢ (spectrum ℂ a) at hEq
  rcases (hasBasis_nhdsSet (spectrum ℂ a)).mem_iff.1 hEq with
    ⟨U, ⟨hU, hσU⟩, hUeq⟩
  exact ⟨U, hU, hσU, fun z hz ↦ hUeq hz⟩

/-- Evaluate the functional calculus using any global representative of a
spectrum germ and any admissible contour in an open domain of analyticity.
This removes both representative and contour choices from
`rieszFunctionalCalculus`.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    (a : A) (f : HolomorphicNearSpectrum a) (g : ℂ → ℂ)
    (hgerm : (g : SpectrumGerm a) = f.1) {G : Set ℂ}
    (hG : IsOpen G) (hσG : spectrum ℂ a ⊆ G)
    (hg : DifferentiableOn ℂ g G) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszFunctionalCalculus a f = rieszIntegral D.toCycle a g
``` -/
theorem rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    (a : A) (f : HolomorphicNearSpectrum a) (g : ℂ → ℂ)
    (hgerm : (g : SpectrumGerm a) = f.1) {G : Set ℂ}
    (hG : IsOpen G) (hσG : spectrum ℂ a ⊆ G)
    (hg : DifferentiableOn ℂ g G) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszFunctionalCalculus a f = rieszIntegral D.toCycle a g := by
  obtain ⟨U, hU, hσU, hEq⟩ := f.exists_open_eqOn_rep a g hgerm
  let H : Set ℂ := U ∩ f.analyticDomain a ∩ G
  have hH : IsOpen H := (hU.inter (f.isOpen_analyticDomain a)).inter hG
  have hσH : spectrum ℂ a ⊆ H := fun z hz ↦
    ⟨⟨hσU hz, f.spectrum_subset_analyticDomain a hz⟩, hσG hz⟩
  obtain ⟨E, hE⟩ := GridFilling.exists_isAdmissibleFor
    (spectrum.isCompact a) hH hσH
  have hErep : E.IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a) :=
    hE.mono_right fun z hz ↦ hz.1.2
  have hEG : E.IsAdmissibleFor (spectrum ℂ a) G :=
    hE.mono_right fun z hz ↦ hz.2
  calc
    rieszFunctionalCalculus a f = rieszIntegral E.toCycle a (f.rep a) :=
      rieszFunctionalCalculus_eq_rieszIntegral_rep a f E hErep
    _ = rieszIntegral E.toCycle a g := by
      apply rieszIntegral_congr_of_eqOn_reducedTrace
      intro z hz
      exact hEq (hE.1 hz).1.1.1
    _ = rieszIntegral D.toCycle a g :=
      rieszIntegral_eq_of_isAdmissibleFor hEG hD hg

/-- Evaluate the functional calculus by the Riesz integral of a globally
defined function analytic on an open neighborhood of the spectrum.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_ofFunction_eq_rieszIntegral
    (a : A) (g : ℂ → ℂ) {G : Set ℂ}
    (hG : IsOpen G) (hσG : spectrum ℂ a ⊆ G)
    (hg : DifferentiableOn ℂ g G) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a g
          ((hg.analyticOnNhd hG).mono hσG)) =
      rieszIntegral D.toCycle a g
``` -/
theorem rieszFunctionalCalculus_ofFunction_eq_rieszIntegral
    (a : A) (g : ℂ → ℂ) {G : Set ℂ}
    (hG : IsOpen G) (hσG : spectrum ℂ a ⊆ G)
    (hg : DifferentiableOn ℂ g G) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a g
          ((hg.analyticOnNhd hG).mono hσG)) =
      rieszIntegral D.toCycle a g := by
  exact rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq a _ g rfl
    hG hσG hg D hD

/-!
### Algebra structure

These are the additive, scalar, and multiplicative clauses of the basic functional-calculus laws.
Preservation of one is kept with the remaining normalization results used to
build the eventual algebra homomorphism.
-/

/-- The Riesz functional calculus preserves addition of holomorphic germs.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_add (a : A)
    (f g : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (f + g) =
      rieszFunctionalCalculus a f + rieszFunctionalCalculus a g
``` -/
@[simp]
theorem rieszFunctionalCalculus_add (a : A)
    (f g : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (f + g) =
      rieszFunctionalCalculus a f + rieszFunctionalCalculus a g := by
  let G : Set ℂ := f.analyticDomain a ∩ g.analyticDomain a
  have hG : IsOpen G := (f.isOpen_analyticDomain a).inter
    (g.isOpen_analyticDomain a)
  have hσG : spectrum ℂ a ⊆ G := fun z hz =>
    ⟨f.spectrum_subset_analyticDomain a hz,
      g.spectrum_subset_analyticDomain a hz⟩
  obtain ⟨D, hD⟩ := GridFilling.exists_isAdmissibleFor
    (spectrum.isCompact a) hG hσG
  have hfG : DifferentiableOn ℂ (f.rep a) G :=
    (f.differentiableOn_analyticDomain a).mono inter_subset_left
  have hgG : DifferentiableOn ℂ (g.rep a) G :=
    (g.differentiableOn_analyticDomain a).mono inter_subset_right
  have hfgG : DifferentiableOn ℂ (f.rep a + g.rep a) G := hfG.add hgG
  have hsumGerm :
      ((f.rep a + g.rep a : ℂ → ℂ) : SpectrumGerm a) = (f + g).1 :=
    (HolomorphicNearSpectrum.rep_add_germ a f g).symm.trans
      ((f + g).rep_germ a)
  have hsum := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a (f + g) (f.rep a + g.rep a) hsumGerm hG hσG hfgG D hD
  have hf := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a f (f.rep a) (f.rep_germ a) hG hσG hfG D hD
  have hg := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a g (g.rep a) (g.rep_germ a) hG hσG hgG D hD
  have hfcont : ContinuousOn (rieszIntegrand a (f.rep a)) D.reducedTrace :=
    (differentiableOn_rieszIntegrand hfG).continuousOn.mono hD.1
  have hgcont : ContinuousOn (rieszIntegrand a (g.rep a)) D.reducedTrace :=
    (differentiableOn_rieszIntegrand hgG).continuousOn.mono hD.1
  have hadd := D.toCycle_integral_add hfcont hgcont
  have hintegrand : rieszIntegrand a (f.rep a + g.rep a) =
      rieszIntegrand a (f.rep a) + rieszIntegrand a (g.rep a) := by
    funext z
    simp [rieszIntegrand, add_smul]
  have hRiesz :
      rieszIntegral D.toCycle a (f.rep a + g.rep a) =
        rieszIntegral D.toCycle a (f.rep a) +
          rieszIntegral D.toCycle a (g.rep a) := by
    change (((2 * Real.pi : ℂ) * Complex.I)⁻¹) •
        D.toCycle.integral (rieszIntegrand a (f.rep a + g.rep a)) =
      (((2 * Real.pi : ℂ) * Complex.I)⁻¹) •
          D.toCycle.integral (rieszIntegrand a (f.rep a)) +
        (((2 * Real.pi : ℂ) * Complex.I)⁻¹) •
          D.toCycle.integral (rieszIntegrand a (g.rep a))
    rw [hintegrand, hadd, smul_add]
  calc
    rieszFunctionalCalculus a (f + g) =
        rieszIntegral D.toCycle a (f.rep a + g.rep a) := hsum
    _ = rieszIntegral D.toCycle a (f.rep a) +
        rieszIntegral D.toCycle a (g.rep a) := hRiesz
    _ = rieszFunctionalCalculus a f + rieszFunctionalCalculus a g := by
      rw [← hf, ← hg]

/-- The Riesz functional calculus preserves multiplication in the displayed order, including for a
noncommutative target algebra.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_mul (a : A)
    (f g : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (f * g) =
      rieszFunctionalCalculus a f * rieszFunctionalCalculus a g
``` -/
@[simp]
theorem rieszFunctionalCalculus_mul (a : A)
    (f g : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (f * g) =
      rieszFunctionalCalculus a f * rieszFunctionalCalculus a g := by
  let G : Set ℂ := f.analyticDomain a ∩ g.analyticDomain a
  have hG : IsOpen G := (f.isOpen_analyticDomain a).inter
    (g.isOpen_analyticDomain a)
  have hσG : spectrum ℂ a ⊆ G := fun z hz ↦
    ⟨f.spectrum_subset_analyticDomain a hz,
      g.spectrum_subset_analyticDomain a hz⟩
  have hfG : DifferentiableOn ℂ (f.rep a) G :=
    (f.differentiableOn_analyticDomain a).mono inter_subset_left
  have hgG : DifferentiableOn ℂ (g.rep a) G :=
    (g.differentiableOn_analyticDomain a).mono inter_subset_right
  have hfgG : DifferentiableOn ℂ (f.rep a * g.rep a) G := hfG.mul hgG
  obtain ⟨D, hD, hDregion⟩ := GridFilling.exists_isAdmissibleFor_with_region_subset
    (spectrum.isCompact a) hG hσG
  have hcompact : IsCompact (spectrum ℂ a ∪ D.region) :=
    (spectrum.isCompact a).union D.isCompact_region
  have hsubset : spectrum ℂ a ∪ D.region ⊆ G :=
    Set.union_subset hσG hDregion
  obtain ⟨H, hH, hHregion⟩ := GridFilling.exists_isAdmissibleFor_with_region_subset
    hcompact hG hsubset
  have hHσ : H.IsAdmissibleFor (spectrum ℂ a) G :=
    hH.mono_left Set.subset_union_left
  have hmulGerm :
      ((f.rep a * g.rep a : ℂ → ℂ) : SpectrumGerm a) = (f * g).1 :=
    (HolomorphicNearSpectrum.rep_mul_germ a f g).symm.trans
      ((f * g).rep_germ a)
  have hfg := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a (f * g) (f.rep a * g.rep a) hmulGerm hG hσG hfgG D hD
  have hf := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a f (f.rep a) (f.rep_germ a) hG hσG hfG D hD
  have hg := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a g (g.rep a) (g.rep_germ a) hG hσG hgG H hHσ
  let C : ℂ := ((2 * Real.pi : ℂ) * Complex.I)⁻¹
  let x : ℂ → A := rieszIntegrand a (f.rep a)
  let y : ℂ → A := rieszIntegrand a (g.rep a)
  let F : ℂ → ℂ → A := fun z ζ ↦ x z * y ζ
  let P : ℂ → ℂ → A := fun z ζ ↦
    (g.rep a ζ * (ζ - z)⁻¹) • x z
  let Q : ℂ → ℂ → A := fun z ζ ↦
    (f.rep a z * (ζ - z)⁻¹) • y ζ
  let target : ℂ → A := rieszIntegrand a (f.rep a * g.rep a)
  have hxcont : ContinuousOn x D.reducedTrace := by
    exact (differentiableOn_rieszIntegrand hfG).continuousOn.mono hD.1
  have hycont : ContinuousOn y H.reducedTrace := by
    exact (differentiableOn_rieszIntegrand hgG).continuousOn.mono hHσ.1
  have hfcont : ContinuousOn (f.rep a) D.reducedTrace :=
    hfG.continuousOn.mono fun z hz ↦ (hD.1 hz).1
  have hgcont : ContinuousOn (g.rep a) H.reducedTrace :=
    hgG.continuousOn.mono fun z hz ↦ (hH.1 hz).1
  have hxprod : ContinuousOn (fun p : ℂ × ℂ ↦ x p.1)
      (D.reducedTrace ×ˢ H.reducedTrace) :=
    hxcont.comp continuous_fst.continuousOn fun p hp ↦ hp.1
  have hyprod : ContinuousOn (fun p : ℂ × ℂ ↦ y p.2)
      (D.reducedTrace ×ˢ H.reducedTrace) :=
    hycont.comp continuous_snd.continuousOn fun p hp ↦ hp.2
  have hfprod : ContinuousOn (fun p : ℂ × ℂ ↦ f.rep a p.1)
      (D.reducedTrace ×ˢ H.reducedTrace) :=
    hfcont.comp continuous_fst.continuousOn fun p hp ↦ hp.1
  have hgprod : ContinuousOn (fun p : ℂ × ℂ ↦ g.rep a p.2)
      (D.reducedTrace ×ˢ H.reducedTrace) :=
    hgcont.comp continuous_snd.continuousOn fun p hp ↦ hp.2
  have hkprod : ContinuousOn (fun p : ℂ × ℂ ↦ (p.2 - p.1)⁻¹)
      (D.reducedTrace ×ˢ H.reducedTrace) := by
    apply (continuousOn_snd.sub continuousOn_fst).inv₀
    intro p hp
    have hpD : p.1 ∈ D.region := D.reducedTrace_subset_region hp.1
    have hpH : p.2 ∉ D.region := fun hpHr ↦
      (hH.1 hp.2).2 (Set.mem_union_right (spectrum ℂ a) hpHr)
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hpD hpH).symm
  have hPcont : ContinuousOn (Function.uncurry P)
      (D.reducedTrace ×ˢ H.reducedTrace) := by
    exact (hgprod.mul hkprod).smul hxprod
  have hQcont : ContinuousOn (Function.uncurry Q)
      (D.reducedTrace ×ˢ H.reducedTrace) := by
    exact (hfprod.mul hkprod).smul hyprod
  have hresolvent : Set.EqOn (Function.uncurry F)
      (Function.uncurry fun z ζ ↦ P z ζ - Q z ζ)
      (D.reducedTrace ×ˢ H.reducedTrace) := by
    rintro ⟨z, ζ⟩ ⟨hz, hζ⟩
    have hzres : z ∈ resolventSet ℂ a := by
      exact spectrum.mem_resolventSet_iff.mpr
        (spectrum.notMem_iff.mp (hD.1 hz).2)
    have hζres : ζ ∈ resolventSet ℂ a := by
      exact spectrum.mem_resolventSet_iff.mpr <| spectrum.notMem_iff.mp fun hζσ ↦
        (hH.1 hζ).2 (Set.mem_union_left D.region hζσ)
    have hzregion : z ∈ D.region := D.reducedTrace_subset_region hz
    have hζregion : ζ ∉ D.region := fun hζD ↦
      (hH.1 hζ).2 (Set.mem_union_right (spectrum ℂ a) hζD)
    have hzζ : z ≠ ζ := ne_of_mem_of_not_mem hzregion hζregion
    have hres := resolvent_mul_resolvent hzres hζres hzζ
    dsimp [F, P, Q, x, y, rieszIntegrand]
    calc
      (f.rep a z • resolvent a z) * (g.rep a ζ • resolvent a ζ) =
          (f.rep a z * g.rep a ζ) •
            (resolvent a z * resolvent a ζ) := smul_mul_smul _ _ _ _
      _ = (f.rep a z * g.rep a ζ) •
          ((ζ - z)⁻¹ • (resolvent a z - resolvent a ζ)) := by rw [hres]
      _ = (g.rep a ζ * (ζ - z)⁻¹) •
            (f.rep a z • resolvent a z) -
          (f.rep a z * (ζ - z)⁻¹) •
            (g.rep a ζ • resolvent a ζ) := by
        simp only [smul_smul, smul_sub]
        apply congrArg₂ (· - ·)
        · apply congrArg (fun c : ℂ ↦ c • resolvent a z)
          ring
        · apply congrArg (fun c : ℂ ↦ c • resolvent a ζ)
          ring
  have hinnerMul (z : ℂ) :
      H.toCycle.integral (F z) = x z * H.toCycle.integral y := by
    let L : A →L[ℂ] A := ContinuousLinearMap.mulLeftRight ℂ A (x z) 1
    have h := H.toCycle_integral_comp_comm L y hycont
    simpa [F, L] using h
  have hdouble :
      D.toCycle.integral (fun z ↦ H.toCycle.integral (F z)) =
        D.toCycle.integral x * H.toCycle.integral y := by
    calc
      _ = D.toCycle.integral (fun z ↦ x z * H.toCycle.integral y) := by
        apply congrArg (D.toCycle.integral)
        funext z
        exact hinnerMul z
      _ = _ := by
        let L : A →L[ℂ] A := ContinuousLinearMap.mulLeftRight ℂ A 1
          (H.toCycle.integral y)
        have h := D.toCycle_integral_comp_comm L x hxcont
        simpa [L] using h
  have hnormalizedProduct :
      rieszIntegral D.toCycle a (f.rep a) *
          rieszIntegral H.toCycle a (g.rep a) =
        C • (C • D.toCycle.integral (fun z ↦ H.toCycle.integral (F z))) := by
    change (C • D.toCycle.integral x) * (C • H.toCycle.integral y) = _
    rw [smul_mul_smul, hdouble, smul_smul]
  have hPparam : ContinuousOn (fun z ↦ H.toCycle.integral (P z))
      D.reducedTrace := H.continuousOn_toCycle_integral_param P hPcont
  have hQparam : ContinuousOn (fun z ↦ H.toCycle.integral (Q z))
      D.reducedTrace := H.continuousOn_toCycle_integral_param Q hQcont
  have hinnerSplit (z : ℂ) (hz : z ∈ D.reducedTrace) :
      H.toCycle.integral (F z) =
        H.toCycle.integral (P z) - H.toCycle.integral (Q z) := by
    calc
      _ = H.toCycle.integral (fun ζ ↦ P z ζ - Q z ζ) := by
        apply H.toCycle_integral_congr_reducedTrace
        intro ζ hζ
        exact @hresolvent (z, ζ) ⟨hz, hζ⟩
      _ = _ := H.toCycle_integral_sub
        (hPcont.uncurry_left z hz) (hQcont.uncurry_left z hz)
  have hsplit :
      D.toCycle.integral (fun z ↦ H.toCycle.integral (F z)) =
        D.toCycle.integral (fun z ↦ H.toCycle.integral (P z)) -
          D.toCycle.integral (fun z ↦ H.toCycle.integral (Q z)) := by
    calc
      _ = D.toCycle.integral (fun z ↦
          H.toCycle.integral (P z) - H.toCycle.integral (Q z)) := by
        apply D.toCycle_integral_congr_reducedTrace
        exact hinnerSplit
      _ = _ := D.toCycle_integral_sub hPparam hQparam
  have hPpoint (z : ℂ) (hz : z ∈ D.reducedTrace) :
      C • H.toCycle.integral (P z) = target z := by
    have hzregion : z ∈ D.region := D.reducedTrace_subset_region hz
    have hzG : z ∈ G := hDregion hzregion
    have hztrace : z ∉ H.reducedTrace := fun hzH ↦
      (hH.1 hzH).2 (Set.mem_union_right (spectrum ℂ a) hzregion)
    have hzindex : H.toCycle.index z = 1 :=
      hH.2.1 z (Set.mem_union_right (spectrum ℂ a) hzregion)
    let s : ℂ → ℂ := fun ζ ↦ g.rep a ζ * (ζ - z)⁻¹
    have hscont : ContinuousOn s H.reducedTrace := by
      apply hgcont.mul
      apply (continuousOn_id.sub continuousOn_const).inv₀
      intro ζ hζ
      exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hztrace)
    have hcauchy : C * H.toCycle.integral s = g.rep a z := by
      simpa [C, s] using H.toCycle_cauchy_formula hG hHregion hgG
        hzG hztrace hzindex
    let L : ℂ →L[ℂ] A :=
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (x z)
    have htransport := H.toCycle_integral_comp_comm L s hscont
    have htransport' : H.toCycle.integral (P z) =
        H.toCycle.integral s • x z := by
      simpa [P, s, L] using htransport
    calc
      C • H.toCycle.integral (P z) =
          C • (H.toCycle.integral s • x z) := by rw [htransport']
      _ = (C * H.toCycle.integral s) • x z := by rw [smul_smul]
      _ = g.rep a z • x z := by rw [hcauchy]
      _ = target z := by
        simp [target, x, rieszIntegrand, smul_smul, mul_comm]
  have hPnormalized :
      C • D.toCycle.integral (fun z ↦ H.toCycle.integral (P z)) =
        D.toCycle.integral target := by
    have hscale := D.toCycle_integral_smul C
      (fun z ↦ H.toCycle.integral (P z)) hPparam
    calc
      _ = D.toCycle.integral
          (fun z ↦ C • H.toCycle.integral (P z)) := hscale.symm
      _ = _ := D.toCycle_integral_congr_reducedTrace hPpoint
  have hQinnerZero (ζ : ℂ) (hζ : ζ ∈ H.reducedTrace) :
      D.toCycle.integral (fun z ↦ Q z ζ) = 0 := by
    have hζregion : ζ ∉ D.region := fun hζD ↦
      (hH.1 hζ).2 (Set.mem_union_right (spectrum ℂ a) hζD)
    let r : ℂ → ℂ := fun z ↦ f.rep a z * (ζ - z)⁻¹
    have hdenom : DifferentiableOn ℂ (fun z ↦ (ζ - z)⁻¹) D.region := by
      intro z hz
      exact (((differentiableAt_const ζ).sub differentiableAt_id).inv
        (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hζregion).symm)).differentiableWithinAt
    have hrdiff : DifferentiableOn ℂ r D.region :=
      (hfG.mono hDregion).mul hdenom
    have hrzero : D.toCycle.integral r = 0 :=
      D.toCycle_integral_eq_zero_of_differentiableOn_region hrdiff
    let L : ℂ →L[ℂ] A :=
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (y ζ)
    have htransport := D.toCycle_integral_comp_comm L r
      (hrdiff.continuousOn.mono D.reducedTrace_subset_region)
    calc
      D.toCycle.integral (fun z ↦ Q z ζ) = L (D.toCycle.integral r) := by
        simpa [Q, r, L] using htransport
      _ = 0 := by rw [hrzero]; simp
  have hQzero :
      D.toCycle.integral (fun z ↦ H.toCycle.integral (Q z)) = 0 := by
    rw [D.toCycle_integral_swap H Q hQcont]
    calc
      H.toCycle.integral (fun ζ ↦ D.toCycle.integral (fun z ↦ Q z ζ)) =
          H.toCycle.integral (0 : ℂ → A) := by
        apply H.toCycle_integral_congr_reducedTrace
        exact hQinnerZero
      _ = 0 := H.toCycle_integral_zero
  have hRiesz :
      rieszIntegral D.toCycle a (f.rep a) *
          rieszIntegral H.toCycle a (g.rep a) =
        rieszIntegral D.toCycle a (f.rep a * g.rep a) := by
    calc
      _ = C • (C • D.toCycle.integral
          (fun z ↦ H.toCycle.integral (F z))) := hnormalizedProduct
      _ = C • (C • (D.toCycle.integral
          (fun z ↦ H.toCycle.integral (P z)) -
            D.toCycle.integral (fun z ↦ H.toCycle.integral (Q z)))) := by rw [hsplit]
      _ = C • (C • D.toCycle.integral
          (fun z ↦ H.toCycle.integral (P z))) := by rw [hQzero, sub_zero]
      _ = C • D.toCycle.integral target := by rw [hPnormalized]
      _ = _ := by rfl
  calc
    rieszFunctionalCalculus a (f * g) =
        rieszIntegral D.toCycle a (f.rep a * g.rep a) := hfg
    _ = rieszIntegral D.toCycle a (f.rep a) *
        rieszIntegral H.toCycle a (g.rep a) := hRiesz.symm
    _ = rieszFunctionalCalculus a f * rieszFunctionalCalculus a g := by
      rw [← hf, ← hg]

/-- The Riesz functional calculus preserves complex scalar multiplication.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_smul (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (c • f) = c • rieszFunctionalCalculus a f
``` -/
@[simp]
theorem rieszFunctionalCalculus_smul (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (c • f) = c • rieszFunctionalCalculus a f := by
  let G : Set ℂ := f.analyticDomain a
  let D : GridFilling := f.contour a
  have hD : D.IsAdmissibleFor (spectrum ℂ a) G := f.contour_isAdmissibleFor a
  have hG : IsOpen G := f.isOpen_analyticDomain a
  have hσG : spectrum ℂ a ⊆ G := f.spectrum_subset_analyticDomain a
  have hfG : DifferentiableOn ℂ (f.rep a) G :=
    f.differentiableOn_analyticDomain a
  have hcfG : DifferentiableOn ℂ (c • f.rep a) G := hfG.const_smul c
  have hsmulGerm :
      ((c • f.rep a : ℂ → ℂ) : SpectrumGerm a) = (c • f).1 :=
    (HolomorphicNearSpectrum.rep_const_smul_germ a c f).symm.trans
      ((c • f).rep_germ a)
  have hcf := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a (c • f) (c • f.rep a) hsmulGerm hG hσG hcfG D hD
  have hf := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a f (f.rep a) (f.rep_germ a) hG hσG hfG D hD
  have hfcont : ContinuousOn (rieszIntegrand a (f.rep a)) D.reducedTrace :=
    (differentiableOn_rieszIntegrand hfG).continuousOn.mono hD.1
  have hsmul := D.toCycle_integral_smul c (rieszIntegrand a (f.rep a)) hfcont
  have hintegrand : rieszIntegrand a (c • f.rep a) =
      c • rieszIntegrand a (f.rep a) := by
    funext z
    simp [rieszIntegrand, smul_smul]
  have hRiesz : rieszIntegral D.toCycle a (c • f.rep a) =
      c • rieszIntegral D.toCycle a (f.rep a) := by
    change (((2 * Real.pi : ℂ) * Complex.I)⁻¹) •
        D.toCycle.integral (rieszIntegrand a (c • f.rep a)) =
      c • ((((2 * Real.pi : ℂ) * Complex.I)⁻¹) •
        D.toCycle.integral (rieszIntegrand a (f.rep a)))
    rw [hintegrand, hsmul, smul_smul, smul_smul]
    congr 1
    exact mul_comm _ _
  calc
    rieszFunctionalCalculus a (c • f) =
        rieszIntegral D.toCycle a (c • f.rep a) := hcf
    _ = c • rieszIntegral D.toCycle a (f.rep a) := hRiesz
    _ = c • rieszFunctionalCalculus a f := by rw [← hf]

/-- The zero holomorphic germ has Riesz value zero.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_zero (a : A) :
    rieszFunctionalCalculus a 0 = 0
``` -/
@[simp]
theorem rieszFunctionalCalculus_zero (a : A) :
    rieszFunctionalCalculus a 0 = 0 := by
  have h := rieszFunctionalCalculus_smul a 0
    (0 : HolomorphicNearSpectrum a)
  simpa using h

/-- The complex-linear map from holomorphic spectrum germs to their Riesz values in the complete
normed algebra.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed. -/
noncomputable def rieszFunctionalCalculusLinearMap (a : A) :
    HolomorphicNearSpectrum a →ₗ[ℂ] A where
  toFun := rieszFunctionalCalculus a
  map_add' := rieszFunctionalCalculus_add a
  map_smul' := rieszFunctionalCalculus_smul a

/-- The bundled linear map has the stated functional-calculus value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculusLinearMap_apply (a : A)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculusLinearMap a f = rieszFunctionalCalculus a f
``` -/
@[simp]
theorem rieszFunctionalCalculusLinearMap_apply (a : A)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculusLinearMap a f = rieszFunctionalCalculus a f :=
  rfl

/-!
### Normalization
-/

/-- the constant-function normalization: the Riesz functional calculus sends the constant-one
germ to the identity of the Banach algebra.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_one (a : A) :
    rieszFunctionalCalculus a (1 : HolomorphicNearSpectrum a) = 1
``` -/
@[simp]
theorem rieszFunctionalCalculus_one (a : A) :
    rieszFunctionalCalculus a (1 : HolomorphicNearSpectrum a) = 1 := by
  let f : HolomorphicNearSpectrum a := 1
  let D : GridFilling := f.contour a
  have hD : D.IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a) :=
    f.contour_isAdmissibleFor a
  have hgerm :
      ((fun _ : ℂ ↦ (1 : ℂ)) : SpectrumGerm a) = f.1 := by
    rfl
  have hEval := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a f (fun _ : ℂ ↦ (1 : ℂ)) hgerm
      (f.isOpen_analyticDomain a) (f.spectrum_subset_analyticDomain a)
      (differentiableOn_const (1 : ℂ)) D hD
  calc
    rieszFunctionalCalculus a (1 : HolomorphicNearSpectrum a) =
        rieszIntegral D.toCycle a (fun _ : ℂ ↦ (1 : ℂ)) := by
      simpa [f] using hEval
    _ = 1 := rieszIntegral_one_of_isAdmissibleFor hD

/-- the coordinate-function normalization: the Riesz functional calculus sends the coordinate
germ to the Banach-algebra element.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_coordinate (a : A) :
    rieszFunctionalCalculus a (HolomorphicNearSpectrum.coordinate a) = a
``` -/
@[simp]
theorem rieszFunctionalCalculus_coordinate (a : A) :
    rieszFunctionalCalculus a (HolomorphicNearSpectrum.coordinate a) = a := by
  let f : HolomorphicNearSpectrum a := HolomorphicNearSpectrum.coordinate a
  let D : GridFilling := f.contour a
  have hD : D.IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a) :=
    f.contour_isAdmissibleFor a
  have hgerm : ((id : ℂ → ℂ) : SpectrumGerm a) = f.1 := by
    rfl
  have hEval := rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    a f id hgerm (f.isOpen_analyticDomain a)
      (f.spectrum_subset_analyticDomain a) differentiableOn_id D hD
  calc
    rieszFunctionalCalculus a (HolomorphicNearSpectrum.coordinate a) =
        rieszIntegral D.toCycle a id := by
      simpa [f] using hEval
    _ = a := rieszIntegral_id_of_isAdmissibleFor hD

/-- The complex algebra homomorphism assigning each holomorphic spectrum germ its Riesz value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed. -/
noncomputable def rieszFunctionalCalculusAlgHom (a : A) :
    HolomorphicNearSpectrum a →ₐ[ℂ] A :=
  AlgHom.ofLinearMap (rieszFunctionalCalculusLinearMap a)
    (by simp)
    (fun f g ↦ by simp)

/-- The bundled algebra homomorphism has the stated functional-calculus value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculusAlgHom_apply (a : A)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculusAlgHom a f = rieszFunctionalCalculus a f
``` -/
@[simp]
theorem rieszFunctionalCalculusAlgHom_apply (a : A)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculusAlgHom a f = rieszFunctionalCalculus a f :=
  rfl
