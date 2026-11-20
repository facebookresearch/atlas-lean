/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicBoundaryRadialRegularity
import Code.Universality.IsingFermionicBoundaryRadialInterpolation
import Code.Universality.IsingFermionicDiscreteInterpolation










open Filter Metric Set Topology

noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


theorem isingProj_sub (e x y : Complex) :
    isingProj e x - isingProj e y = isingProj e (x - y) := by
  unfold isingProj
  rw [map_sub]
  ring


theorem isingProj_norm_le (e z : Complex) (he : Complex.normSq e = 1) :
    ‖isingProj e z‖ ≤ ‖z‖ := by
  have hpair := isingProj_normSq_add_neg e z he
  have hnonneg := Complex.normSq_nonneg (isingProj (-e) z)
  have hsq : Complex.normSq (isingProj e z) ≤ Complex.normSq z := by
    linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem isingProj_dist_le (e x y : Complex) (he : Complex.normSq e = 1) :
    dist (isingProj e x) (isingProj e y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, isingProj_sub]
  exact isingProj_norm_le e (x - y) he



theorem isingProj_dist_le_of_nearby_holder
    (e : Complex) (F : Complex → Complex)
    (sample embedded observable : Complex) (C alpha : NNReal)
    (he : Complex.normSq e = 1) (hholder : HolderWith C alpha F)
    (hsample : isingProj e (F sample) = observable) :
    dist (isingProj e (F embedded)) observable ≤
      C * dist embedded sample ^ (alpha : Real) := by
  rw [← hsample]
  exact (isingProj_dist_le e (F embedded) (F sample) he).trans
    (hholder.dist_le embedded sample)



theorem norm_sub_le_two_mul_of_proj_one_I
    (x y z : Complex)
    (hxy : isingProj 1 x = isingProj 1 y)
    (hyz : isingProj Complex.I y = isingProj Complex.I z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyRe := congrArg Complex.re hxy
  have hyzRe := congrArg Complex.re hyz
  simp [isingProj] at hxyRe hyzRe
  have hre : x.re = y.re := by linarith
  have him : y.im = y.re - z.re + z.im := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [hre, him]
    nlinarith [sq_nonneg (y.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((y.re - z.re) + (x.im - z.im)),
      sq_nonneg ((y.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith

theorem norm_sub_le_two_mul_of_proj_I_negOne
    (x y z : Complex)
    (hxy : isingProj Complex.I x = isingProj Complex.I y)
    (hyz : isingProj (-1) y = isingProj (-1) z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyRe := congrArg Complex.re hxy
  have hyzIm := congrArg Complex.im hyz
  simp [isingProj] at hxyRe hyzIm
  have him : y.im = z.im := by linarith
  have hre : x.re - y.re = x.im - y.im := by linarith
  have hre' : x.re - y.re = x.im - z.im := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [him, hre']
    nlinarith [sq_nonneg (x.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((x.re - z.re) + (x.im - z.im)),
      sq_nonneg ((x.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith

theorem norm_sub_le_two_mul_of_proj_negOne_negI
    (x y z : Complex)
    (hxy : isingProj (-1) x = isingProj (-1) y)
    (hyz : isingProj (-Complex.I) y = isingProj (-Complex.I) z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyIm := congrArg Complex.im hxy
  have hyzRe := congrArg Complex.re hyz
  simp [isingProj] at hxyIm hyzRe
  have him : x.im = y.im := by linarith
  have hre : y.re = z.re + z.im - y.im := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [him, hre]
    nlinarith [sq_nonneg (x.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((x.re - z.re) + (x.im - z.im)),
      sq_nonneg ((x.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith

theorem norm_sub_le_two_mul_of_proj_negI_one
    (x y z : Complex)
    (hxy : isingProj (-Complex.I) x = isingProj (-Complex.I) y)
    (hyz : isingProj 1 y = isingProj 1 z) :
    ‖x - y‖ ≤ 2 * ‖x - z‖ := by
  have hxyRe := congrArg Complex.re hxy
  have hyzRe := congrArg Complex.re hyz
  simp [isingProj] at hxyRe hyzRe
  have hre : y.re = z.re := by linarith
  have him : x.im - y.im = y.re - x.re := by linarith
  have him' : x.im - y.im = z.re - x.re := by linarith
  have hsq : Complex.normSq (x - y) ≤ 4 * Complex.normSq (x - z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    rw [hre, him']
    nlinarith [sq_nonneg (x.re - z.re), sq_nonneg (x.im - z.im),
      sq_nonneg ((x.re - z.re) + (x.im - z.im)),
      sq_nonneg ((x.re - z.re) - (x.im - z.im))]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith




theorem IsingSquareSHolomorphicQuad.projection_cycle
    (north east south west : Complex)
    (h : IsingSquareSHolomorphicQuad south west north east) :
    isingProj 1 north = isingProj 1 east ∧
      isingProj Complex.I east = isingProj Complex.I south ∧
      isingProj (-1) south = isingProj (-1) west ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  rcases h with ⟨h1, h2, h3⟩
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  have h2re := congrArg Complex.re h2
  have h2im := congrArg Complex.im h2
  have h3re := congrArg Complex.re h3
  have h3im := congrArg Complex.im h3
  simp at h1re h1im h2re h2im h3re h3im
  unfold isingProj
  constructor
  · apply Complex.ext <;> simp <;> linarith
  constructor
  · apply Complex.ext <;> simp <;> linarith
  constructor
  · apply Complex.ext <;> simp <;> linarith
  · apply Complex.ext <;> simp <;> linarith



theorem projectionCycle_crossParity_norm_sub_le
    (north east south west : Complex) (delta : Real)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hNS : ‖north - south‖ ≤ delta)
    (hEW : ‖east - west‖ ≤ delta) :
    ‖north - east‖ ≤ 2 * delta ∧
      ‖east - south‖ ≤ 2 * delta ∧
      ‖south - west‖ ≤ 2 * delta ∧
      ‖west - north‖ ≤ 2 * delta := by
  constructor
  · exact (norm_sub_le_two_mul_of_proj_one_I north east south hNE hES).trans
      (mul_le_mul_of_nonneg_left hNS (by norm_num))
  constructor
  · exact (norm_sub_le_two_mul_of_proj_I_negOne east south west hES hSW).trans
      (mul_le_mul_of_nonneg_left hEW (by norm_num))
  constructor
  · have h := norm_sub_le_two_mul_of_proj_negOne_negI south west north hSW hWN
    rw [norm_sub_rev] at hNS
    exact h.trans (mul_le_mul_of_nonneg_left hNS (by norm_num))
  · have h := norm_sub_le_two_mul_of_proj_negI_one west north east hWN hNE
    rw [norm_sub_rev] at hEW
    exact h.trans (mul_le_mul_of_nonneg_left hEW (by norm_num))



theorem fkIsingSquareBoundaryRadialPatchFullObservable_even_projectionCycle
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    isingProj 1 north = isingProj 1 east ∧
      isingProj Complex.I east = isingProj Complex.I south ∧
      isingProj (-1) south = isingProj (-1) west ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  exact IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
    (fkIsingSquareBoundaryRadialPatchFullObservable_quad
      n m i j hn hm hi0 hi1 hj0 hj1 heven)



theorem fkIsingSquareBoundaryRadialPatchFullObservable_odd_projectionCycle
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    isingProj 1 south = isingProj 1 west ∧
      isingProj Complex.I west = isingProj Complex.I north ∧
      isingProj (-1) north = isingProj (-1) east ∧
      isingProj (-Complex.I) east = isingProj (-Complex.I) south := by
  exact IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
    (fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd
      n m i j hn hm hi0 hi1 hj0 hj1 hodd)

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)




structure MeshUniformFullHolder (F : Nat → Complex → Complex) where
  constant : NNReal
  exponent : NNReal
  exponent_pos : 0 < exponent
  holder : ∀ n, HolderWith constant exponent (F n)

theorem MeshUniformFullHolder.equicontinuous
    {F : Nat → Complex → Complex} (H : MeshUniformFullHolder F) :
    Equicontinuous F := by
  apply UniformEquicontinuous.equicontinuous
  apply Metric.uniformEquicontinuous_of_continuity_modulus
    (fun d : Real => (H.constant : Real) * d ^ (H.exponent : Real))
  · have hp : (0 : Real) < (H.exponent : Real) := H.exponent_pos
    have ht := (Real.continuousAt_rpow_const 0 (H.exponent : Real)
      (Or.inr hp.le)).tendsto.const_mul (H.constant : Real)
    simpa [Real.zero_rpow hp.ne'] using ht
  · intro x y n
    exact (H.holder n).dist_le x y




structure BoundaryRadialTensorTentGeometry where
  n : Nat → Nat
  m : Nat → Nat
  hn : ∀ k, 0 < n k
  hm : ∀ k, m k ≤ n k
  i : ∀ k, A.M k → Fin (m k)
  j : ∀ k, A.M k → Fin (m k)
  side : ∀ k, A.M k → FKIsingMedialSide
  embedding_eq : ∀ k e,
    A.medialEmbedding k e =
      isingRadialGridPosition (A.mesh k) (i k e).1 (j k e).1
  observable_eq : ∀ k e,
    @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P k) (A.M k) (A.decEqM k) (A.dobrushin k) (A.mesh k) e =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain (n k) (hn k)).normalizedFermionicObservable
        (A.mesh k)
          (.dart (fkIsingSquareRadialPatchEdge
            (n k) (m k) (hm k) (i k e) (j k e), side k e))


noncomputable def BoundaryRadialTensorTentGeometry.interpolant
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) :
    Nat → Complex → Complex := fun k =>
  fkIsingSquareBoundaryRadialPatchInterpolant
    (G.n k) (G.m k) (G.hn k) (G.hm k) (A.mesh k)


noncomputable def BoundaryRadialTensorTentGeometry.tangent
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A)
    (k : Nat) (e : A.M k) : Complex :=
  fkIsingSquareWiredDirectedTangent (G.n k) (G.hn k)
    (.dart (fkIsingSquareRadialPatchEdge
      (G.n k) (G.m k) (G.hm k) (G.i k e) (G.j k e), G.side k e))

theorem BoundaryRadialTensorTentGeometry.interpolant_continuous
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) (k : Nat) :
    Continuous (BoundaryRadialTensorTentGeometry.interpolant A G k) :=
  fkIsingSquareBoundaryRadialPatchInterpolant_continuous
    (G.n k) (G.m k) (G.hn k) (G.hm k) (A.mesh k)

theorem BoundaryRadialTensorTentGeometry.projectedMedial
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) (k : Nat) (e : A.M k) :
    isingProj
        (BoundaryRadialTensorTentGeometry.tangent A G k e)
        (BoundaryRadialTensorTentGeometry.interpolant A G k
          (A.medialEmbedding k e)) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P k) (A.M k) (A.decEqM k) (A.dobrushin k) (A.mesh k) e := by
  rw [G.embedding_eq k e]
  simp only [BoundaryRadialTensorTentGeometry.tangent,
    BoundaryRadialTensorTentGeometry.interpolant]
  rw [fkIsingSquareBoundaryRadialPatchInterpolant_projection
    (G.n k) (G.m k) (G.hn k) (G.hm k) (A.mesh k)
    (A.mesh_pos k) (G.i k e) (G.j k e) (G.side k e)]
  exact (G.observable_eq k e).symm



structure StableFullMedialInterpolation
    (tangent : ∀ n, A.M n → Complex) where
  interpolant : Nat → Complex → Complex
  continuousOn : ∀ n, ContinuousOn (interpolant n) A.U
  projectedMedial : ∀ n e,
    isingProj (tangent n e) (interpolant n (A.medialEmbedding n e)) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e
  compactEquicontinuous : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    EquicontinuousOn interpolant K



noncomputable def StableFullMedialInterpolation.ofTensorTent
    (tangent : ∀ n, A.M n → Complex)
    (F : Nat → Complex → Complex)
    (hcontinuous : ∀ n, Continuous (F n))
    (hprojected : ∀ n e,
      isingProj (tangent n e) (F n (A.medialEmbedding n e)) =
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
    (hholder : MeshUniformFullHolder F) :
    A.StableFullMedialInterpolation tangent where
  interpolant := F
  continuousOn n := (hcontinuous n).continuousOn
  projectedMedial := hprojected
  compactEquicontinuous K _hK _hKU :=
    hholder.equicontinuous.equicontinuousOn K



noncomputable def BoundaryRadialTensorTentGeometry.toStableFullMedialInterpolation
    (G : BoundaryRadialTensorTentGeometry A)
    (H : MeshUniformFullHolder
      (BoundaryRadialTensorTentGeometry.interpolant A G)) :
    A.StableFullMedialInterpolation
      (BoundaryRadialTensorTentGeometry.tangent A G) :=
  StableFullMedialInterpolation.ofTensorTent A
    (BoundaryRadialTensorTentGeometry.tangent A G)
    (BoundaryRadialTensorTentGeometry.interpolant A G)
    (BoundaryRadialTensorTentGeometry.interpolant_continuous A G)
    (BoundaryRadialTensorTentGeometry.projectedMedial A G) H

variable {tangent : ∀ n, A.M n → Complex}
variable (I : A.StableFullMedialInterpolation tangent)

def StableFullMedialInterpolation.HasCompactLocalBounds : Prop :=
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ C : Real, ∀ n z, z ∈ K → ‖I.interpolant n z‖ ≤ C



theorem StableFullMedialInterpolation.hasCompactLocalBounds_of_holder_anchor
    (H : MeshUniformFullHolder I.interpolant)
    (B : Real) (hanchor : ∀ n, ‖I.interpolant n A.root‖ ≤ B) :
    I.HasCompactLocalBounds := by
  intro K hK _hKU
  have hdistContinuous : Continuous (fun z : Complex => dist z A.root) :=
    continuous_id.dist continuous_const
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    hdistContinuous.continuousOn
  refine ⟨B + (H.constant : Real) * D ^ (H.exponent : Real), ?_⟩
  intro n z hz
  calc
    ‖I.interpolant n z‖ ≤ ‖I.interpolant n A.root‖ +
        ‖I.interpolant n z - I.interpolant n A.root‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ = ‖I.interpolant n A.root‖ +
        dist (I.interpolant n z) (I.interpolant n A.root) := by
      rw [dist_eq_norm]
    _ ≤ B + (H.constant : Real) * dist z A.root ^ (H.exponent : Real) :=
      add_le_add (hanchor n) ((H.holder n).dist_le z A.root)
    _ ≤ B + (H.constant : Real) * D ^ (H.exponent : Real) := by
      gcongr
      simpa [Real.norm_of_nonneg dist_nonneg] using hD z hz

theorem StableFullMedialInterpolation.locallyUniformlySequentiallyPrecompact
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds) :
    StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact
      I.interpolant A.U :=
  StatMech.FrontierA.equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    I.interpolant A.U A.isOpen I.compactEquicontinuous hbounded E

def StableFullMedialInterpolation.SubsequentialMoreraPrimitive
    (target Phi : Complex → Complex) : Prop :=
  ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
    StrictMono phi → StrictMono psi →
    TendstoLocallyUniformlyOn
      (fun n => I.interpolant (phi (psi n))) f atTop A.U →
    Complex.IsConservativeOn f A.U ∧
    ∃ (P : Complex → Complex) (C : Real),
      DifferentiableOn Complex P A.U ∧
      Set.EqOn (deriv P) (fun z => f z ^ 2) A.U ∧
      (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧
      f A.root = target A.root

theorem StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds)
    (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  apply StatMech.FrontierA.tendstoLocallyUniformlyOn_of_subsequential_limits_unique
    I.interpolant target A.U A.isOpen
    (StableFullMedialInterpolation.locallyUniformlySequentiallyPrecompact
      A I E hbounded)
  intro phi psi f hphi hpsi hlimit
  obtain ⟨hMorera, P, C, hP, hPderiv, him, hanchor⟩ :=
    hidentify phi psi f hphi hpsi hlimit
  have hfContinuous : ContinuousOn f A.U :=
    hlimit.continuousOn (Filter.Frequently.of_forall
      (fun n => I.continuousOn (phi (psi n))))
  have hf : DifferentiableOn Complex f A.U :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      A.isOpen).1 ⟨hMorera, hfContinuous⟩
  have hsquare := isingFermionic_square_eq_of_primitive_im_eq
    f target P Phi A.U A.root C A.isOpen A.isPreconnected A.root_mem
      hP hPhi hPderiv hPhideriv him
  exact isingFermionic_squareRoot_unique_of_anchor
    f target A.U A.root A.isOpen A.isPreconnected A.root_mem hf htarget
      hsquare hanchor htarget_ne




theorem StableFullMedialInterpolation.scalingLimit_of_tensorTentGridHolder
    (H : MeshUniformFullHolder I.interpolant)
    (B : Real) (hanchorBound : ∀ n, ‖I.interpolant n A.root‖ ≤ B)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  exact StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    A I target Phi htarget htarget_ne hPhi hPhideriv E
      (StableFullMedialInterpolation.hasCompactLocalBounds_of_holder_anchor
        A I H B hanchorBound) hidentify



theorem StableFullMedialInterpolation.projectedLiteralObservable_tendsto_on_compacts
    (hunit : ∀ n e, Complex.normSq (tangent n e) = 1)
    (target : Complex → Complex)
    (hlimit : TendstoLocallyUniformlyOn I.interpolant target atTop A.U)
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ e : A.M n, A.medialEmbedding n e ∈ K →
      dist
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
        (isingProj (tangent n e) (target (A.medialEmbedding n e))) < epsilon := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact A.isOpen] at hlimit
  have hKlimit := hlimit K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hKlimit
  filter_upwards [hKlimit epsilon hepsilon] with n hn
  intro e he
  rw [← I.projectedMedial n e]
  exact lt_of_le_of_lt
    (isingProj_dist_le (tangent n e)
      (I.interpolant n (A.medialEmbedding n e))
      (target (A.medialEmbedding n e)) (hunit n e))
    (by simpa only [dist_comm] using hn (A.medialEmbedding n e) he)

end FKIsingCaratheodoryApproximation

end StatMech.Universality

end
