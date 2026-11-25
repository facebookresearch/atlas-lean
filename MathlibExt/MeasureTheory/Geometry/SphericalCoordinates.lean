/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Spherical coordinates

Two planar polar transformations, coordinate permutations, and a shift of the azimuth
produce the spherical-coordinate map. The two planar Jacobians multiply to the spherical
weight, and the image misses at most a null plane. Applying the Bochner change-of-variables
formula avoids any integrability assumption on the original function.
-/

noncomputable section

open Set MeasureTheory

namespace MathlibExt.MeasureTheory.Geometry.SphericalCoordinatesWanted

private def domain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < 2 * Real.pi ∧ 0 < p.2.2 ∧ p.2.2 < Real.pi}

private def spherical (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1 * Real.sin p.2.2 * Real.cos p.2.1,
    p.1 * Real.sin p.2.2 * Real.sin p.2.1, p.1 * Real.cos p.2.2)

private theorem polar_symm_mem (r t : ℝ) (hr : 0 < r) (hlt : -Real.pi < t)
    (hgt : t < Real.pi) : (r, t) ∈ polarCoord.target := ⟨hr, hlt, hgt⟩

private theorem domain_measurable : MeasurableSet domain := by
  have h : domain = Ioi (0 : ℝ) ×ˢ (Ioo 0 (2 * Real.pi) ×ˢ Ioo 0 Real.pi) := by
    ext p
    simp [domain, and_assoc]
  rw [h]
  exact measurableSet_Ioi.prod (measurableSet_Ioo.prod measurableSet_Ioo)

private theorem planar (p : ℝ × ℝ × ℝ) :
    polarCoord.symm (p.1 * Real.sin p.2.2, p.2.1 - Real.pi) =
      (-(spherical p).1, -(spherical p).2.1) := by
  simp [polarCoord, spherical, Real.cos_sub_pi, Real.sin_sub_pi]

private theorem meridian (p : ℝ × ℝ × ℝ) :
    polarCoord.symm (p.1, p.2.2) = ((spherical p).2.2, p.1 * Real.sin p.2.2) := rfl

-- First recover the projected radius and azimuth, then recover the radius and inclination.
private theorem spherical_injOn : InjOn spherical domain := by
  intro p hp q hq hpq
  rcases hp with ⟨hpr, hpt, hpt', hpp, hpp'⟩
  rcases hq with ⟨hqr, hqt, hqt', hqp, hqp'⟩
  have pplan := polar_symm_mem (p.1 * Real.sin p.2.2) (p.2.1 - Real.pi)
    (mul_pos hpr (Real.sin_pos_of_pos_of_lt_pi hpp hpp')) (by linarith) (by linarith)
  have qplan := polar_symm_mem (q.1 * Real.sin q.2.2) (q.2.1 - Real.pi)
    (mul_pos hqr (Real.sin_pos_of_pos_of_lt_pi hqp hqp')) (by linarith) (by linarith)
  have eplan := polarCoord.symm.injOn pplan qplan (by rw [planar, planar, hpq])
  have eρ : p.1 * Real.sin p.2.2 = q.1 * Real.sin q.2.2 := congrArg Prod.fst eplan
  have eθ' : p.2.1 - Real.pi = q.2.1 - Real.pi := congrArg Prod.snd eplan
  have eθ : p.2.1 = q.2.1 := by linarith
  have pmer := polar_symm_mem p.1 p.2.2 hpr (by linarith [Real.pi_pos]) hpp'
  have qmer := polar_symm_mem q.1 q.2.2 hqr (by linarith [Real.pi_pos]) hqp'
  have emer := polarCoord.symm.injOn pmer qmer (by rw [meridian, meridian, hpq, eρ])
  simp only [Prod.mk.injEq] at emer
  exact Prod.ext emer.1 (Prod.ext eθ emer.2)

-- The two inverse planar charts give preimages off the middle-coordinate plane.
private theorem spherical_image_superset :
    {p : ℝ × ℝ × ℝ | p.2.1 ≠ 0} ⊆ spherical '' domain := by
  rintro ⟨x, y, z⟩ hy
  change y ≠ 0 at hy
  have hxy : (-x, -y) ∈ polarCoord.source := by
    change 0 < -x ∨ -y ≠ 0
    exact Or.inr (neg_ne_zero.mpr hy)
  obtain ⟨⟨ρ, t⟩, hρt, eρt⟩ := polarCoord.symm_image_target_eq_source.symm ▸ hxy
  have hρ : 0 < ρ := hρt.1
  have hzρ : (z, ρ) ∈ polarCoord.source := by
    change 0 < z ∨ ρ ≠ 0
    exact Or.inr hρ.ne'
  obtain ⟨⟨r, φ⟩, hrφ, erφ⟩ := polarCoord.symm_image_target_eq_source.symm ▸ hzρ
  have eρ : r * Real.sin φ = ρ := congrArg Prod.snd erφ
  have ez : r * Real.cos φ = z := congrArg Prod.fst erφ
  have hp : 0 < φ := by
    by_contra! hφ
    have hsin := Real.sin_nonpos_of_nonpos_of_neg_pi_le hφ hrφ.2.1.le
    have := mul_nonpos_of_nonneg_of_nonpos hrφ.1.le hsin
    linarith
  refine ⟨(r, t + Real.pi, φ), ⟨hrφ.1, ?_, ?_, hp, hrφ.2.2⟩, ?_⟩
  · linarith [hρt.2.1]
  · linarith [hρt.2.2]
  have hh : polarCoord.symm (r * Real.sin φ, (t + Real.pi) - Real.pi) = (-x, -y) := by
    rw [eρ, add_sub_cancel_right, eρt]
  rw [planar (r, t + Real.pi, φ)] at hh
  exact Prod.ext (neg_injective (congrArg Prod.fst hh))
    (Prod.ext (neg_injective (congrArg Prod.snd hh)) ez)

open ContinuousLinearMap

private abbrev Triple := ℝ × ℝ × ℝ

private def first : Triple →L[ℝ] ℝ := fst ℝ ℝ (ℝ × ℝ)
private def tail : Triple →L[ℝ] (ℝ × ℝ) := snd ℝ ℝ (ℝ × ℝ)
private def second : Triple →L[ℝ] ℝ := (fst ℝ ℝ ℝ).comp tail
private def third : Triple →L[ℝ] ℝ := (snd ℝ ℝ ℝ).comp tail

private def swap12 : Triple →L[ℝ] Triple := second.prod (first.prod third)
private def swap23 : Triple →L[ℝ] Triple := first.prod (third.prod second)
private def rotate : Triple →L[ℝ] Triple := swap23.comp swap12
private def negTail : Triple →L[ℝ] Triple := first.prod (-tail)

private theorem abs_det_involution (A : Triple →L[ℝ] Triple)
    (hA : A.comp A = ContinuousLinearMap.id ℝ Triple) : |A.det| = 1 := by
  have h := congrArg (fun g : Triple →L[ℝ] Triple => g.det) hA
  change LinearMap.det (A.toLinearMap.comp A.toLinearMap) = LinearMap.det LinearMap.id at h
  rw [LinearMap.det_comp, LinearMap.det_id] at h
  rw [← abs_one, abs_eq_iff_mul_self_eq, one_mul]
  exact h

private theorem abs_det_swap12 : |swap12.det| = 1 :=
  abs_det_involution swap12 (by ext <;> rfl)

private theorem abs_det_swap23 : |swap23.det| = 1 :=
  abs_det_involution swap23 (by ext <;> rfl)

private theorem abs_det_negTail : |negTail.det| = 1 :=
  abs_det_involution negTail (by ext <;> simp [negTail, first, tail])

private theorem abs_det_comp (A B : Triple →L[ℝ] Triple) :
    |(A.comp B).det| = |A.det| * |B.det| := by
  change |LinearMap.det (A.toLinearMap.comp B.toLinearMap)| = _
  rw [LinearMap.det_comp, abs_mul]

private theorem abs_det_rotate : |rotate.det| = 1 := by
  rw [rotate, abs_det_comp, abs_det_swap23, abs_det_swap12, mul_one]

private def polarLift : Triple → Triple := Prod.map id polarCoord.symm

private def polarLiftD (p : Triple) : Triple →L[ℝ] Triple :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (fderivPolarCoordSymm p.2)

private theorem hasFDerivAt_polarLift (p : Triple) :
    HasFDerivAt polarLift (polarLiftD p) p :=
  HasFDerivAt.prodMap p (hasFDerivAt_id p.1) (hasFDerivAt_polarCoord_symm p.2)

private theorem det_polarLift (p : Triple) : (polarLiftD p).det = p.2.1 := by
  change LinearMap.det ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
    (fderivPolarCoordSymm p.2).toLinearMap) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  exact det_fderivPolarCoordSymm p.2

private def shifted (p : Triple) : Triple := (p.1, p.2.1, p.2.2 - Real.pi)

private theorem hasFDerivAt_shifted (p : Triple) :
    HasFDerivAt shifted (ContinuousLinearMap.id ℝ Triple) p := by
  convert (hasFDerivAt_id (𝕜 := ℝ) p).sub_const (0, 0, Real.pi) using 1
  funext q
  simp [shifted, Prod.sub_def]

-- The first polar map is in the meridian plane. Its positive horizontal radius enters
-- the second polar map; shifting the azimuth by π uses the pinned principal angle.
private def polarInput (p : Triple) : Triple := shifted (rotate (polarLift (swap12 p)))

private theorem spherical_eq_comp :
    spherical = fun p => rotate (negTail (polarLift (polarInput p))) := by
  funext p
  symm
  change (-(p.1 * Real.sin p.2.2 * Real.cos (p.2.1 - Real.pi)),
    -(p.1 * Real.sin p.2.2 * Real.sin (p.2.1 - Real.pi)), p.1 * Real.cos p.2.2) = spherical p
  simp [spherical, Real.cos_sub_pi, Real.sin_sub_pi]

private def polarInputD (p : Triple) : Triple →L[ℝ] Triple :=
  rotate.comp ((polarLiftD (swap12 p)).comp swap12)

private theorem hasFDerivAt_polarInput (p : Triple) :
    HasFDerivAt polarInput (polarInputD p) p := by
  have hpolar : HasFDerivAt (fun q => polarLift (swap12 q))
      ((polarLiftD (swap12 p)).comp swap12) p :=
    (hasFDerivAt_polarLift (swap12 p)).comp p swap12.hasFDerivAt
  have hrot : HasFDerivAt (fun q => rotate (polarLift (swap12 q))) (polarInputD p) p :=
    (rotate.hasFDerivAt (x := polarLift (swap12 p))).comp p hpolar
  change HasFDerivAt (shifted ∘ fun q : Triple => rotate (polarLift (swap12 q))) (polarInputD p) p
  simpa only [id_comp] using
    (hasFDerivAt_shifted (rotate (polarLift (swap12 p)))).comp p hrot

private def sphericalD (p : Triple) : Triple →L[ℝ] Triple :=
  rotate.comp (negTail.comp ((polarLiftD (polarInput p)).comp (polarInputD p)))

private theorem hasFDerivAt_chain {f g : Triple → Triple} {df dg : Triple →L[ℝ] Triple}
    {p : Triple} (hg : HasFDerivAt g dg (f p)) (hf : HasFDerivAt f df p) :
    HasFDerivAt (g ∘ f) (dg.comp df) p := hg.comp p hf

private theorem hasFDerivAt_spherical (p : Triple) :
    HasFDerivAt spherical (sphericalD p) p := by
  have hpol := hasFDerivAt_chain (hasFDerivAt_polarLift (polarInput p)) (hasFDerivAt_polarInput p)
  have hneg := hasFDerivAt_chain (p := p) (f := polarLift ∘ polarInput)
    (negTail.hasFDerivAt (x := polarLift (polarInput p))) hpol
  have h := hasFDerivAt_chain (p := p) (f := (negTail : Triple → Triple) ∘ polarLift ∘ polarInput)
    (rotate.hasFDerivAt (x := negTail (polarLift (polarInput p)))) hneg
  have heq : spherical = (rotate : Triple → Triple) ∘ negTail ∘ polarLift ∘ polarInput :=
    spherical_eq_comp
  exact Eq.mpr (congrArg (fun f : Triple → Triple => HasFDerivAt f (sphericalD p) p) heq) h

private theorem abs_det_spherical (p : Triple) (hp : p ∈ domain) :
    |(sphericalD p).det| = p.1 ^ 2 * Real.sin p.2.2 := by
  rcases hp with ⟨hr, _, _, hφ, hφ'⟩
  have hρ : 0 < p.1 * Real.sin p.2.2 := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hφ hφ')
  simp only [sphericalD, polarInputD, abs_det_comp, abs_det_swap12, abs_det_negTail,
    abs_det_rotate, det_polarLift, mul_one, one_mul]
  change |p.1 * Real.sin p.2.2| * |p.1| = _
  rw [abs_of_pos hρ, abs_of_pos hr]
  ring

local instance : (volume : Measure Triple).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure (ℝ × ℝ))

private theorem coordinate_plane_null : volume {p : Triple | p.2.1 = 0} = 0 := by
  change volume (↑second.toLinearMap.ker : Set Triple) = 0
  apply Measure.addHaar_submodule
  rw [Ne, LinearMap.ker_eq_top]
  intro h
  have he : second (0, 1, 0) = 0 := DFunLike.congr_fun h (0, 1, 0)
  exact one_ne_zero he

private theorem spherical_image_ae : spherical '' domain =ᵐ[volume] (univ : Set Triple) := by
  have h : ∀ᵐ p : Triple ∂volume, p.2.1 ≠ 0 := ae_iff.mpr (by simpa using coordinate_plane_null)
  filter_upwards [h] with p hp
  simp only [mem_univ, iff_true]
  exact spherical_image_superset hp

private theorem integral_spherical
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Triple → E) :
    (∫ p in domain, (p.1 ^ 2 * Real.sin p.2.2 : ℝ) • f (spherical p)) = ∫ p, f p := by
  calc
    _ = ∫ p in domain, |(sphericalD p).det| • f (spherical p) :=
      setIntegral_congr_fun domain_measurable fun p hp => by rw [abs_det_spherical p hp]
    _ = ∫ p in spherical '' domain, f p :=
      (integral_image_eq_integral_abs_det_fderiv_smul volume domain_measurable
        (fun p _ => (hasFDerivAt_spherical p).hasFDerivWithinAt) spherical_injOn f).symm
    _ = ∫ p, f p := by rw [setIntegral_congr_set spherical_image_ae, setIntegral_univ]

/-- **Change of variables to spherical coordinates.** Let $E$ be a real Banach space and let
$f \colon \mathbb{R}^3 \to E$ be any function. Then the integral of $f$ over $\mathbb{R}^3$
equals the integral over the set of $(r, \theta, \varphi) \in \mathbb{R}^3$ with $r > 0$,
$0 < \theta < 2\pi$ and $0 < \varphi < \pi$ of
$r^2 \sin\varphi \cdot f(r \sin\varphi \cos\theta,\, r \sin\varphi \sin\theta,\, r \cos\varphi)$,
both integrals being Bochner integrals with respect to Lebesgue measure.

No integrability hypothesis is assumed; as usual for Bochner integrals, a non-integrable
function has integral $0$. This is the three-dimensional analogue of the polar-coordinate
change of variables.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Measures and integral calculus /
  Integration", entry "change of variables to spherical co-ordinates"
  (no declaration linked in the pinned Mathlib list).
- W. Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 8, Exercise 6, pp. 175–176
  (related radial integration formula for nonnegative Borel functions; see dimensions two
  and three).
- https://en.wikipedia.org/wiki/Spherical_coordinate_system#Integration_and_differentiation_in_spherical_coordinates
-/
public theorem integral_comp_spherical_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ × ℝ × ℝ → E) :
    (∫ p in {p : ℝ × ℝ × ℝ |
        0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < 2 * Real.pi ∧ 0 < p.2.2 ∧ p.2.2 < Real.pi},
      (p.1 ^ 2 * Real.sin p.2.2 : ℝ) •
        f (p.1 * Real.sin p.2.2 * Real.cos p.2.1,
          p.1 * Real.sin p.2.2 * Real.sin p.2.1, p.1 * Real.cos p.2.2)) =
      ∫ p, f p := by
  exact integral_spherical f

end MathlibExt.MeasureTheory.Geometry.SphericalCoordinatesWanted
