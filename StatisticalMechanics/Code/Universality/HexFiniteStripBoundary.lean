/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























import Code.Universality.HexBoundaryIdentityClose
import Code.Universality.HexContourDefs
import Code.Universality.HexFiniteRegion

namespace StatMech.Universality

open Complex HexWalk
open scoped BigOperators

variable {V : Type*} [DecidableEq V]



noncomputable def hexFiniteStripRaw (Fa : ℝ)
    (alphaRest betaSum epsSum epsbarSum : ℂ) : ℂ :=
  -((Fa : ℂ) + alphaRest) + betaSum
    + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum











structure HexFiniteStripBoundaryData (R : HexFiniteRegion) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing) where
  
  sides : HexContourSides
  
  interior_sub : P.interior ⊆ D.incidences
  
  vertex_mem : ∀ v ∈ D.interiorVertices, D.pos v ∈ R.verts
  
  mid_mem : ∀ e ∈ D.incidences, D.mid e.vtx e.edge ∈ R.mids
  
  obs_eq : ∀ z, D.obs z =
    parafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  
  lam : ℝ
  
  tau : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  
  lam_eq : lam = hexContourLambda R.inRegion R.start h0 sides hexChi
  
  tau_eq : tau = hexContourTauPlus R.inRegion R.start h0 sides hexChi
    + hexContourTauMinus R.inRegion R.start h0 sides hexChi
  
  ups_eq : ups = hexContourUpsilon R.inRegion R.start h0 sides hexChi
  
  Fa_eq : (Fa : ℂ) = D.obs R.start
  
  alphaRest : ℂ
  alphaRest_eq : alphaRest
    = (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
        + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2 * (lam : ℂ)
  
  betaSum : ℂ
  betaSum_eq : betaSum = (ups : ℂ)
  
  epsSum : ℂ
  epsSum_eq : epsSum
    = Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
        * ((tau / 2 : ℝ) : ℂ)
  
  epsbarSum : ℂ
  epsbarSum_eq : epsbarSum
    = Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)
        * ((tau / 2 : ℝ) : ℂ)
  
  contour_eq : D.boundarySum P =
    hexFiniteStripRaw Fa alphaRest betaSum epsSum epsbarSum

namespace HexFiniteStripBoundaryData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P)




theorem raw_eq_zero :
    hexFiniteStripRaw B.Fa B.alphaRest B.betaSum B.epsSum B.epsbarSum = 0 := by
  have hraw := D.hexBoundaryRaw P B.interior_sub
  rw [B.contour_eq] at hraw
  exact hraw



noncomputable def toFObsBoundaryData :
    HexFObsBoundaryData where
  lam := B.lam
  ups := B.ups
  tau := B.tau
  Fa := B.Fa
  alphaRest := B.alphaRest
  alphaRest_eq := B.alphaRest_eq
  betaSum := B.betaSum
  betaSum_eq := B.betaSum_eq
  epsSum := B.epsSum
  epsSum_eq := B.epsSum_eq
  epsbarSum := B.epsbarSum
  epsbarSum_eq := B.epsbarSum_eq
  raw := by
    change hexFiniteStripRaw B.Fa B.alphaRest B.betaSum B.epsSum B.epsbarSum = 0
    exact B.raw_eq_zero



theorem boundary_identity (hFa : B.Fa = 1) :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = 1 :=
  B.toFObsBoundaryData.boundaryIdentity hFa



theorem contour_boundary_identity (hFa : B.Fa = 1) :
    hexBdryCl * hexContourLambda R.inRegion R.start h0 B.sides hexChi
      + hexBdryCt *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)
      + hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
  rw [← B.lam_eq, ← B.tau_eq, ← B.ups_eq]
  exact B.boundary_identity hFa

end HexFiniteStripBoundaryData



theorem hexFiniteStrip_boundary_identity_scales
    (R : ℕ → HexFiniteRegion) (h0 : ℕ → ℤ)
    (D : ℕ → HexDomain V) (P : ∀ v, (D v).InteriorPairing)
    (B : ∀ v, HexFiniteStripBoundaryData (R v) (h0 v) (D v) (P v))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (B v).lam + hexBdryCt * (B v).tau + (B v).ups = 1 := by
  intro v hv
  exact (B v).boundary_identity (hFa v hv)

end StatMech.Universality
