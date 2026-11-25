/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual measured point heights and scalar normalization

The algebraic fibre is the native section module of the actual
scheme-point pullback of the line. At every place its scalar map passes
through the real scheme residue map and native completion unit.
Place vectors agree with every actual pulled-back local section.

Height is the negative integral of the actual logarithmic fibre norm.
Its scalar normalization uses the original field's nonzero
product-formula measure. Independence of the algebraic vector follows
from the actual one-dimensional fibre and that product formula.

Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 4.1--4.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights

open CategoryTheory CategoryTheory.Limits Opposite MeasureTheory
open _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels CoherentCurveLinearSeries
open GenericSectionMaps

variable {K : Type} [Field K] (A : AdelicField K) (X : Over (Spec (.of K)))
  (L : X.left.Modules)

/-- The original rational-point scheme, with its native K scalars. -/
abbrev BasePoint : Over (Spec (.of K)) := Over.mk (𝟙 (Spec (.of K)))

/-- The actual algebraic fibre is the section module of this same pulled-back line. -/
abbrev AlgebraicFibre (x : BasePoint (K := K) ⟶ X) :=
  Sections (BasePoint (K := K)) ((Scheme.Modules.pullback x.left).obj L)

/-- The actual local algebraic section in the scheme-point pullback fibre. -/
def pointSection (x : BasePoint (K := K) ⟶ X) (U : X.left.Opens) (s : Γ(L,U))
    (hx : x.left (IsLocalRing.closedPoint K) ∈ U) : AlgebraicFibre X L x :=
  localPullbackSection x.left L U ⊤ (by
    let : Subsingleton (BasePoint (K := K)).left :=
      inferInstanceAs (Subsingleton (Spec (.of K)))
    intro y hy
    change x.left y ∈ U
    rw [show y = IsLocalRing.closedPoint K from Subsingleton.elim _ _]
    exact hx) s

/-- The actual completed scalar map from K through the point's place residue field. -/
def completedScalars (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) :
    K →+* ValuedLineFibres.CompletedResidue (A.completion v) (placeScheme A X v) p :=
  (ValuedLineFibres.completionUnit _ _ p).comp
    ((BerkovichAnalytification.scalarMap (A.completion v) (placeScheme A X v) p.schemePoint).comp
      (A.embedding v))

/-- Its norm is the actual given place absolute value, with no new normalization. -/
theorem completedScalars_norm (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) (a : K) :
    ‖completedScalars A X v p a‖ = ‖A.embedding v a‖ := by
  let b : ValuedLineFibres.Residue (A.completion v) (placeScheme A X v) p :=
    BerkovichAnalytification.scalarMap (A.completion v) (placeScheme A X v)
      p.schemePoint (A.embedding v a)
  change ‖(b : UniformSpace.Completion
    (ValuedLineFibres.Residue (A.completion v) (placeScheme A X v) p))‖ = _
  rw [UniformSpace.Completion.norm_coe]
  exact p.extends_norm _

/-- Actual one-dimensional scheme fibres and their source-normalized place realization. -/
structure PointFrame (x : BasePoint (K := K) ⟶ X) where
  basis : Module.Basis Unit K (AlgebraicFibre X L x)
  point : ∀ v : A.places, ValuedLineFibres.Point (A.completion v) (placeScheme A X v)
  scheme_normalized : ∀ v,
    placeProjection A X v (point v).schemePoint = x.left (IsLocalRing.closedPoint K)
  vector : ∀ v, AlgebraicFibre X L x →ₛₗ[completedScalars A X v (point v)]
    ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v) (placeLine A X L v) (point v)
  injective : ∀ v, Function.Injective (vector v)
  section_normalized : ∀ (U : X.left.Opens) (s : Γ(L,U))
    (hx : x.left (IsLocalRing.closedPoint K) ∈ U) (v : A.places),
    vector v (pointSection X L x U s hx) =
      ValuedLineFibres.evaluateSection _ _ _ (RationalAdelicModelMetrics.placeSection U s v)
        (point v) (by
          change placeProjection A X v (point v).schemePoint ∈ U
          rw [scheme_normalized]
          exact hx)

variable (N : MetrizedLine A X L) {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)

/-- Logarithmic norms use the actual placewise fibre vectors. -/
def logNorm (e : AlgebraicFibre X L x) : A.places → ℝ :=
  fun v ↦ Real.log (norm N v (F.point v) (F.vector v e))

/-- The actual measured height for an algebraic fibre vector. -/
def height (e : AlgebraicFibre X L x) : ℝ := -∫ v, logNorm A X L N F e v ∂A.measure

/-- Integrability is retained on these actual fibre evaluations. -/
def IsAdmissible : Prop := ∀ e : AlgebraicFibre X L x, e ≠ 0 →
  Integrable (logNorm A X L N F e) A.measure

/-- Every nonzero algebraic scalar contributes exactly its given place logarithm. -/
theorem logNorm_smul (a : K) (ha : a ≠ 0) (e : AlgebraicFibre X L x) (he : e ≠ 0)
    (v : A.places) :
    logNorm A X L N F (a • e) v =
      Real.log ‖A.embedding v a‖ + logNorm A X L N F e v := by
  rw [logNorm, F.vector v |>.map_smulₛₗ]
  change Real.log (((N.metric v).fibreNorm (F.point v)).norm
    (completedScalars A X v (F.point v) a • F.vector v e)) = _
  rw [ValuedLineFibres.FibreNorm.homogeneous, completedScalars_norm]
  have hn : 0 < norm N v (F.point v) (F.vector v e) := by
    apply lt_of_le_of_ne (((N.metric v).fibreNorm (F.point v)).nonnegative (F.vector v e))
    intro hz
    apply he
    apply F.injective v
    simpa only [map_zero] using (norm_zero_iff N v (F.point v) _).mp hz.symm
  have hv : A.embedding v a ≠ 0 := by
    simpa only [map_zero] using (RingHom.injective (A.embedding v)).ne ha
  exact Real.log_mul (norm_ne_zero_iff.mpr hv)
    (ne_of_gt hn)

/-- The given nonzero product-formula measure removes every algebraic scalar contribution. -/
theorem height_smul (H : IsAdmissible A X L N F) (a : K) (ha : a ≠ 0)
    (e : AlgebraicFibre X L x) (he : e ≠ 0) :
    height A X L N F (a • e) = height A X L N F e := by
  have h : logNorm A X L N F (a • e) =
      (fun v ↦ Real.log ‖A.embedding v a‖) + logNorm A X L N F e := by
    funext v
    exact logNorm_smul A X L N F a ha e he v
  simp only [height, h, Pi.add_apply]
  rw [integral_add (A.integrable a ha) (H e he), A.product_formula a ha, zero_add]

/-- A nonzero algebraic fibre vector is its actual basis-coordinate scalar multiple. -/
theorem basis_scalar (e : AlgebraicFibre X L x) :
    e = (F.basis.repr e ()) • F.basis () := by
  apply F.basis.repr.injective
  apply Finsupp.ext
  intro i
  cases i
  simp

/-- Heights are independent of the nonzero algebraic fibre vector. -/
theorem height_independent (H : IsAdmissible A X L N F)
    (e f : AlgebraicFibre X L x) (he : e ≠ 0) (hf : f ≠ 0) :
    height A X L N F e = height A X L N F f := by
  have hc (u : AlgebraicFibre X L x) (hu : u ≠ 0) : F.basis.repr u () ≠ 0 := by
    intro h
    apply hu
    rw [basis_scalar A X L F u, h, zero_smul]
  rw [basis_scalar A X L F e, basis_scalar A X L F f]
  rw [height_smul A X L N F H _ (hc e he) _ (F.basis.ne_zero ()),
    height_smul A X L N F H _ (hc f hf) _ (F.basis.ne_zero ())]

/-- The height of the rational point $x$ for the metrized line, assumed admissible (for every
nonzero vector $e$ of the fibre of the line at $x$, the function $v \mapsto \log \lVert e \rVert_v$
is integrable): $h(x) = -\int \log \lVert e \rVert_v \, d\mu(v)$, for the basis vector $e$ of
that fibre given by the frame `F`. -/
def pointHeight (_H : IsAdmissible A X L N F) : ℝ := height A X L N F (F.basis ())

end MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
