/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.PositiveTransferObservable
import Code.Ising.GKS

open Finset Matrix Filter Topology
open scoped BigOperators

namespace StatMech.Ising

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]


def cylinderLayerInteraction
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h : W -> Real)
    (s : ConfigSpace W) : Real :=
  (∑ e ∈ E, J e * bond s e) + ∑ x : W, h x * spin s x


def cylinderInterLayerInteraction
    (Jvertical : W -> Real) (s t : ConfigSpace W) : Real :=
  ∑ x : W, Jvertical x * spin s x * spin t x



def isingCylinderTransfer
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real) :
    Matrix (ConfigSpace W) (ConfigSpace W) Real :=
  fun s t => Real.exp
    (cylinderLayerInteraction E J h s / 2 +
      cylinderInterLayerInteraction Jvertical s t +
      cylinderLayerInteraction E J h t / 2)

theorem cylinderInterLayerInteraction_symm
    (Jvertical : W -> Real) (s t : ConfigSpace W) :
    cylinderInterLayerInteraction Jvertical s t =
      cylinderInterLayerInteraction Jvertical t s := by
  unfold cylinderInterLayerInteraction
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem isingCylinderTransfer_isHermitian
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real) :
    (isingCylinderTransfer E J h Jvertical).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  simp only [isingCylinderTransfer, star_trivial]
  rw [cylinderInterLayerInteraction_symm]
  congr 1
  ring

theorem isingCylinderTransfer_pos
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (s t : ConfigSpace W) :
    0 < isingCylinderTransfer E J h Jvertical s t := Real.exp_pos _


def isingCylinderBoundaryVector
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h : W -> Real)
    (boundary : ConfigSpace W -> Real) (s : ConfigSpace W) : Real :=
  Real.exp (cylinderLayerInteraction E J h s / 2 + boundary s)

theorem isingCylinderBoundaryVector_pos
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h : W -> Real)
    (boundary : ConfigSpace W -> Real) (s : ConfigSpace W) :
    0 < isingCylinderBoundaryVector E J h boundary s := Real.exp_pos _


def isingCylinderPartition
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real) (n : Nat) : Real :=
  let A := isingCylinderTransfer E J h Jvertical
  let a := isingCylinderBoundaryVector E J h leftBoundary
  let ell := isingCylinderBoundaryVector E J h rightBoundary
  ∑ s, ell s * ((A ^ n) *ᵥ a) s


def isingCylinderEndpointMean
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real)
    (obs : ConfigSpace W -> Real) (n : Nat) : Real :=
  let A := isingCylinderTransfer E J h Jvertical
  let a := isingCylinderBoundaryVector E J h leftBoundary
  let ell := isingCylinderBoundaryVector E J h rightBoundary
  (∑ s, ell s * obs s * ((A ^ n) *ᵥ a) s) /
    ∑ s, ell s * ((A ^ n) *ᵥ a) s


theorem isingCylinderEndpointMean_tendsto
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real)
    (obs : ConfigSpace W -> Real) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real (ConfigSpace W),
        (forall s, 0 < u s) ∧ norm u = 1 ∧
        isingCylinderTransfer E J h Jvertical *ᵥ (fun s => u s) =
          lam • (fun s => u s) ∧
        Tendsto
          (isingCylinderEndpointMean E J h Jvertical
            leftBoundary rightBoundary obs)
          atTop
          (nhds ((∑ s,
              isingCylinderBoundaryVector E J h rightBoundary s *
                obs s * u s) /
            ∑ s, isingCylinderBoundaryVector E J h rightBoundary s * u s)) := by
  simpa [isingCylinderEndpointMean] using
    positiveTransfer_endpointObservable_tendsto
      (isingCylinderTransfer E J h Jvertical)
      (isingCylinderTransfer_isHermitian E J h Jvertical)
      (isingCylinderTransfer_pos E J h Jvertical)
      (isingCylinderBoundaryVector E J h leftBoundary)
      (isingCylinderBoundaryVector E J h rightBoundary)
      (isingCylinderBoundaryVector_pos E J h leftBoundary)
      (isingCylinderBoundaryVector_pos E J h rightBoundary) obs


theorem isingCylinderEndpointSpin_tendsto
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real) (x : W) :
    exists m : Real,
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundary rightBoundary (fun s => spin s x))
        atTop (nhds m) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, hlim⟩ :=
    isingCylinderEndpointMean_tendsto E J h Jvertical
      leftBoundary rightBoundary (fun s => spin s x)
  exact ⟨(∑ s, isingCylinderBoundaryVector E J h rightBoundary s *
      spin s x * u s) /
    ∑ s, isingCylinderBoundaryVector E J h rightBoundary s * u s, hlim⟩





theorem isingCylinder_twoBoundaryEndpoint_common
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundaryA leftBoundaryB rightBoundary : ConfigSpace W -> Real)
    (obs : ConfigSpace W -> Real) :
    exists m : Real,
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryA rightBoundary obs) atTop (nhds m) ∧
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryB rightBoundary obs) atTop (nhds m) := by
  simpa [isingCylinderEndpointMean] using
    positiveTransfer_twoBoundary_endpointObservable_common
      (isingCylinderTransfer E J h Jvertical)
      (isingCylinderTransfer_isHermitian E J h Jvertical)
      (isingCylinderTransfer_pos E J h Jvertical)
      (isingCylinderBoundaryVector E J h leftBoundaryA)
      (isingCylinderBoundaryVector E J h leftBoundaryB)
      (isingCylinderBoundaryVector E J h rightBoundary)
      (isingCylinderBoundaryVector_pos E J h leftBoundaryA)
      (isingCylinderBoundaryVector_pos E J h leftBoundaryB)
      (isingCylinderBoundaryVector_pos E J h rightBoundary) obs


theorem isingCylinder_twoBoundarySpin_common
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundaryA leftBoundaryB rightBoundary : ConfigSpace W -> Real)
    (x : W) :
    exists m : Real,
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryA rightBoundary (fun s => spin s x))
        atTop (nhds m) ∧
      Tendsto
        (isingCylinderEndpointMean E J h Jvertical
          leftBoundaryB rightBoundary (fun s => spin s x))
        atTop (nhds m) :=
  isingCylinder_twoBoundaryEndpoint_common E J h Jvertical
    leftBoundaryA leftBoundaryB rightBoundary (fun s => spin s x)


theorem isingCylinderPartition_log_div_tendsto
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real) :
    exists lam : Real, 0 < lam ∧
      Tendsto (fun n : Nat =>
        Real.log (isingCylinderPartition E J h Jvertical
          leftBoundary rightBoundary n) / (n : Real))
        atTop (nhds (Real.log lam)) := by
  simpa [isingCylinderPartition] using
    positiveTransfer_log_dotProduct_div_tendsto
      (isingCylinderTransfer E J h Jvertical)
      (isingCylinderTransfer_isHermitian E J h Jvertical)
      (isingCylinderTransfer_pos E J h Jvertical)
      (isingCylinderBoundaryVector E J h leftBoundary)
      (isingCylinderBoundaryVector E J h rightBoundary)
      (isingCylinderBoundaryVector_pos E J h leftBoundary)
      (isingCylinderBoundaryVector_pos E J h rightBoundary)

end

end StatMech.Ising
