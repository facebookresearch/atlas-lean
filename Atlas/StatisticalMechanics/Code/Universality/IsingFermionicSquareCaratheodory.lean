/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareBoundaryScaledDomain
import Code.Universality.IsingFermionicCaratheodoryApproximation





namespace StatMech.Universality

open Filter Set Topology Metric
open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

private theorem natAbs_le_of_int_bounds {n : Nat} {z : Int}
    (h0 : -(n : Int) ≤ z) (h1 : z ≤ (n : Int)) : z.natAbs ≤ n := by
  have h : |z| ≤ (n : Int) := abs_le.mpr ⟨h0, h1⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h



theorem exists_fkIsingSquareWiredCarrier_scaledPosition_near
    (n : Nat) (hn : 0 < n) (scale : Real) (hscale : 0 < scale)
    (z : Complex)
    (hx0 : -(n : Int) ≤ ⌊z.re / scale⌋)
    (hx1 : ⌊z.re / scale⌋ < (n : Int))
    (hy0 : -(n : Int) ≤ ⌊z.im / scale⌋)
    (hy1 : ⌊z.im / scale⌋ ≤ (n : Int)) :
    ∃ a : FKIsingSquareWiredCarrier n,
      dist z ((scale : Complex) *
        fkIsingSquareWiredCarrierPosition n hn a) < 3 * scale := by
  let x : Int := ⌊z.re / scale⌋
  let y : Int := ⌊z.im / scale⌋
  let u : (fkSquareBoxPlanar n).V :=
    ⟨![x, y], by
      intro k
      fin_cases k
      · change x.natAbs ≤ n
        apply natAbs_le_of_int_bounds
        · simpa [x] using hx0
        · have hx1' : x < (n : Int) := by simpa [x] using hx1
          omega
      · change y.natAbs ≤ n
        exact natAbs_le_of_int_bounds (by simpa [y] using hy0)
          (by simpa [y] using hy1)⟩
  have heast : fkIsingSquareDirectionAvailable n u .east := by
    simp [fkIsingSquareDirectionAvailable, u]
    omega
  let e := fkIsingSquareDirectionEdge n u .east heast
  let a : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let w : Complex :=
    (scale * ((x : Real) + 1 / 2) : Real) +
      Complex.I * (scale * (y : Real) : Real)
  have hposition :
      (scale : Complex) * fkIsingSquareWiredCarrierPosition n hn a = w := by
    simp [a, e, fkIsingSquareWiredCarrierPosition,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition, u, w]
    push_cast
    ring
  have hxfloor : (x : Real) ≤ z.re / scale := by
    exact_mod_cast Int.floor_le (z.re / scale)
  have hxceil : z.re / scale < (x : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (z.re / scale)
  have hyfloor : (y : Real) ≤ z.im / scale := by
    exact_mod_cast Int.floor_le (z.im / scale)
  have hyceil : z.im / scale < (y : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (z.im / scale)
  have hxabs : |z.re - scale * ((x : Real) + 1 / 2)| ≤ scale / 2 := by
    rw [abs_le]
    constructor <;> (field_simp at hxfloor hxceil ⊢ <;> nlinarith)
  have hyabs : |z.im - scale * (y : Real)| < scale := by
    rw [abs_lt]
    constructor <;> (field_simp at hyfloor hyceil ⊢ <;> nlinarith)
  refine ⟨a, ?_⟩
  rw [hposition, dist_eq_norm]
  calc
    ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - scale * ((x : Real) + 1 / 2)| +
        |z.im - scale * (y : Real)| := by simp [w]
    _ < scale / 2 + scale := add_lt_add_of_le_of_lt hxabs hyabs
    _ < 3 * scale := by linarith


def fkIsingExpandingSquareSide (k : Nat) : Nat := (k + 1) ^ 2


def fkIsingExpandingSquareScale (k : Nat) : Real := 1 / (k + 1 : Nat)


def fkIsingExpandingSquareMesh (k : Nat) : Real :=
  4 * fkIsingExpandingSquareScale k

theorem fkIsingExpandingSquareSide_pos (k : Nat) :
    0 < fkIsingExpandingSquareSide k := by
  simp [fkIsingExpandingSquareSide]

theorem fkIsingExpandingSquareScale_pos (k : Nat) :
    0 < fkIsingExpandingSquareScale k := by
  simp [fkIsingExpandingSquareScale]
  positivity

theorem fkIsingExpandingSquareMesh_pos (k : Nat) :
    0 < fkIsingExpandingSquareMesh k := by
  simp [fkIsingExpandingSquareMesh, fkIsingExpandingSquareScale]
  positivity

theorem fkIsingExpandingSquareMesh_tendsto_zero :
    Tendsto fkIsingExpandingSquareMesh atTop (nhds 0) := by
  have hadd : Tendsto (fun k : Nat ↦ k + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hinv : Tendsto (fun k : Nat ↦ (1 : Real) / (k + 1 : Nat))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat.comp hadd
  change Tendsto (fun k : Nat ↦ (4 : Real) * (1 / (k + 1 : Nat)))
    atTop (nhds 0)
  convert (tendsto_const_nhds.mul hinv :
      Tendsto (fun k : Nat ↦ (4 : Real) * (1 / (k + 1 : Nat)))
        atTop (nhds (4 * 0))) using 1 <;> norm_num


def fkIsingExpandingSquareCarrier (k : Nat) : Set Complex :=
  {z | ∃ a : FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k),
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a) ≤
        fkIsingExpandingSquareMesh k}

theorem fkIsingExpandingSquare_compact_eventually_mem
    (K : Set Complex) (hK : IsCompact K) :
    ∀ᶠ k in atTop, K ⊆ fkIsingExpandingSquareCarrier k := by
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  obtain ⟨N : Nat, hN⟩ := exists_nat_gt (max C 0 + 2)
  filter_upwards [eventually_ge_atTop N] with k hk
  intro z hz
  have hzC : dist z 0 ≤ C := by
    simpa [dist_comm] using hC hz
  have hCnonneg : 0 ≤ C := by
    have hdist : 0 ≤ dist z 0 := dist_nonneg
    linarith
  have hzNorm : ‖z‖ ≤ C := by simpa [dist_eq_norm] using hzC
  have hzre : |z.re| ≤ C := (Complex.abs_re_le_norm z).trans hzNorm
  have hzim : |z.im| ≤ C := (Complex.abs_im_le_norm z).trans hzNorm
  let side := fkIsingExpandingSquareSide k
  let scale := fkIsingExpandingSquareScale k
  have hscale : 0 < scale := fkIsingExpandingSquareScale_pos k
  have hklarge : C + 1 < (k + 1 : Nat) := by
    have hkreal : (N : Real) ≤ (k : Real) := by exact_mod_cast hk
    have hCmax : C ≤ max C 0 := le_max_left C 0
    push_cast
    linarith
  have hx0 : -(side : Int) ≤ ⌊z.re / scale⌋ := by
    rw [Int.le_floor]
    have hre := (abs_le.mp hzre).1
    simp [side, scale, fkIsingExpandingSquareSide,
      fkIsingExpandingSquareScale]
    field_simp
    norm_num [Nat.cast_add] at hklarge ⊢
    nlinarith
  have hx1 : ⌊z.re / scale⌋ < (side : Int) := by
    rw [Int.floor_lt]
    have hre := (abs_le.mp hzre).2
    simp [side, scale, fkIsingExpandingSquareSide,
      fkIsingExpandingSquareScale]
    field_simp
    norm_num [Nat.cast_add] at hklarge ⊢
    nlinarith
  have hy0 : -(side : Int) ≤ ⌊z.im / scale⌋ := by
    rw [Int.le_floor]
    have him := (abs_le.mp hzim).1
    simp [side, scale, fkIsingExpandingSquareSide,
      fkIsingExpandingSquareScale]
    field_simp
    norm_num [Nat.cast_add] at hklarge ⊢
    nlinarith
  have hy1 : ⌊z.im / scale⌋ ≤ (side : Int) := by
    have hylt : ⌊z.im / scale⌋ < (side : Int) := by
      rw [Int.floor_lt]
      have him := (abs_le.mp hzim).2
      simp [side, scale, fkIsingExpandingSquareSide,
        fkIsingExpandingSquareScale]
      field_simp
      norm_num [Nat.cast_add] at hklarge ⊢
      nlinarith
    omega
  obtain ⟨a, ha⟩ := exists_fkIsingSquareWiredCarrier_scaledPosition_near
    side (fkIsingExpandingSquareSide_pos k) scale hscale z hx0 hx1 hy0 hy1
  have hpert := fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    side (fkIsingExpandingSquareSide_pos k) scale hscale a
  refine ⟨a, ?_⟩
  change dist z (fkIsingSquareWiredPerturbedCarrierPosition
      side (fkIsingExpandingSquareSide_pos k) scale hscale a) ≤ _
  apply le_of_lt
  calc
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
        side (fkIsingExpandingSquareSide_pos k) scale hscale a) ≤
      dist z ((scale : Complex) *
          fkIsingSquareWiredCarrierPosition
            side (fkIsingExpandingSquareSide_pos k) a) +
        dist ((scale : Complex) *
          fkIsingSquareWiredCarrierPosition
            side (fkIsingExpandingSquareSide_pos k) a)
          (fkIsingSquareWiredPerturbedCarrierPosition
            side (fkIsingExpandingSquareSide_pos k) scale hscale a) :=
      dist_triangle _ _ _
    _ < 3 * scale + scale / 10 :=
      add_lt_add ha (by simpa [dist_comm] using hpert)
    _ ≤ fkIsingExpandingSquareMesh k := by
      simp [fkIsingExpandingSquareMesh, scale]
      linarith




noncomputable def fkIsingExpandingSquareCaratheodoryApproximation :
    FKIsingCaratheodoryApproximation where
  U := Set.univ
  root := 0
  root_mem := Set.mem_univ 0
  isOpen := isOpen_univ
  isPreconnected := isPreconnected_univ
  carrier := fkIsingExpandingSquareCarrier
  mesh := fkIsingExpandingSquareMesh
  mesh_pos := fkIsingExpandingSquareMesh_pos
  mesh_tendsto_zero := fkIsingExpandingSquareMesh_tendsto_zero
  compact_eventually_mem := by
    intro K hK _
    exact fkIsingExpandingSquare_compact_eventually_mem K hK
  exterior_eventually_avoided := by
    intro z hz
    simp at hz
  P := fun k ↦ fkSquareBoxPlanar (fkIsingExpandingSquareSide k)
  M := fun k ↦ FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k)
  fintypeM := fun _ ↦ inferInstance
  decEqM := fun _ ↦ inferInstance
  dobrushin := fun k ↦ fkIsingSquareWiredPerturbedDobrushinDomain
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertexEmbedding := fun k _ ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) .source
  medialEmbedding := fun k ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertex_mem_carrier := by
    intro k v
    refine ⟨.source, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  medial_mem_carrier := by
    intro k a
    refine ⟨a, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  carrier_near_medial := by
    intro k z hz
    exact hz
  medialEmbedding_eq_position := by
    intro k a
    rfl
  rawInterpolant := fun k ↦ fkIsingSquareWiredPerturbedRawInterpolant
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  rawInterpolant_medial := by
    intro k a
    exact fkIsingSquareWiredPerturbedRawInterpolant_medial
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a



noncomputable def fkIsingExpandingBoundarySquareCaratheodoryApproximation :
    FKIsingCaratheodoryApproximation where
  U := Set.univ
  root := 0
  root_mem := Set.mem_univ 0
  isOpen := isOpen_univ
  isPreconnected := isPreconnected_univ
  carrier := fkIsingExpandingSquareCarrier
  mesh := fkIsingExpandingSquareMesh
  mesh_pos := fkIsingExpandingSquareMesh_pos
  mesh_tendsto_zero := fkIsingExpandingSquareMesh_tendsto_zero
  compact_eventually_mem := by
    intro K hK _
    exact fkIsingExpandingSquare_compact_eventually_mem K hK
  exterior_eventually_avoided := by
    intro z hz
    simp at hz
  P := fun k ↦ fkIsingSquareBoundaryDeletedPlanar
    (fkIsingExpandingSquareSide k)
  M := fun k ↦ FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k)
  fintypeM := fun _ ↦ inferInstance
  decEqM := fun _ ↦ inferInstance
  dobrushin := fun k ↦ fkIsingSquareBoundaryPerturbedDobrushinDomain
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertexEmbedding := fun k _ ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) .source
  medialEmbedding := fun k ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertex_mem_carrier := by
    intro k v
    refine ⟨.source, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  medial_mem_carrier := by
    intro k a
    refine ⟨a, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  carrier_near_medial := by
    intro k z hz
    exact hz
  medialEmbedding_eq_position := by
    intro k a
    rfl
  rawInterpolant := fun k ↦ fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  rawInterpolant_medial := by
    intro k a
    exact fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_medial
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a

private def fkIsingSquareDirectionComplexStep :
    FKIsingSquareDirection → Complex
  | .east => 1
  | .north => Complex.I
  | .west => -1
  | .south => -Complex.I

private theorem fkIsingSquareSitePosition_neighbor
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareSitePosition (fkIsingSquareNeighbor n u d hd).1 =
      fkIsingSquareSitePosition u.1 + fkIsingSquareDirectionComplexStep d := by
  cases d <;> apply Complex.ext <;>
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareSitePosition, fkIsingSquareDirectionComplexStep] <;> rfl

private theorem fkIsingSquareDirectionComplexStep_norm
    (d : FKIsingSquareDirection) :
    ‖fkIsingSquareDirectionComplexStep d‖ = 1 := by
  cases d <;> simp [fkIsingSquareDirectionComplexStep]

private theorem fkIsingSquareDirectionEdgeOrientation_position_sum
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareSitePosition
          (fkIsingSquareDirectionEdgeOrientation n u d hd).tail.1 +
        fkIsingSquareSitePosition
          (fkIsingSquareDirectionEdgeOrientation n u d hd).head.1 =
      fkIsingSquareSitePosition u.1 +
        fkIsingSquareSitePosition (fkIsingSquareNeighbor n u d hd).1 := by
  cases d <;>
    simp [fkIsingSquareDirectionEdgeOrientation] <;> ac_rfl

set_option maxHeartbeats 800000 in


theorem fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le
    (n m baseI baseJ R : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) :
    ‖((1 / (m : Real) : Real) : Complex) *
        fkIsingSquareWiredCarrierPosition n (by omega)
          (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p)‖ ≤ 3 := by
  let i : Fin m := ⟨baseI + p.1.1, by have := p.1.2; omega⟩
  let j : Fin m := ⟨baseJ + p.2.1, by have := p.2.2; omega⟩
  let u := fkIsingSquareRadialPatchVertex n m hm i j
  let d := fkIsingSquareRadialPatchDirection i.1 j.1
  let v := fkIsingSquareNeighbor n u d
    (fkIsingSquareRadialPatchDirection_available n m hm i j)
  have hu0 : |((u.1 0 : Int) : Real)| ≤ (m : Real) := by
    simp [u, fkIsingSquareRadialPatchVertex]
    rw [fkIsingSquareRadialPatchHalf_eq]
    have hi := i.2
    have hj := j.2
    omega
  have hu1 : |((u.1 1 : Int) : Real)| ≤ (m : Real) := by
    have hu1eq : u.1 1 = (i.1 : Int) -
        (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      simp only [u, fkIsingSquareRadialPatchVertex]
      rw [fkIsingSquareRadialPatchHalf_eq]
      rfl
    rw [hu1eq]
    have hi := i.2
    have hj := j.2
    have hInt : |(i.1 : Int) - (((i.1 + j.1 + 1) / 2 : Nat) : Int)| ≤
        (m : Int) := by
      rw [abs_le]
      constructor <;> push_cast <;> omega
    exact_mod_cast hInt
  have hupos : ‖fkIsingSquareSitePosition u.1‖ ≤ 2 * (m : Real) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [fkIsingSquareSitePosition]
    linarith
  have hvpos : ‖fkIsingSquareSitePosition v.1‖ ≤ 2 * (m : Real) + 1 := by
    have hvEq : fkIsingSquareSitePosition v.1 = fkIsingSquareSitePosition u.1 +
        fkIsingSquareDirectionComplexStep d :=
      fkIsingSquareSitePosition_neighbor n u d _
    have hstep := fkIsingSquareDirectionComplexStep_norm d
    calc
      ‖fkIsingSquareSitePosition v.1‖ =
          ‖fkIsingSquareSitePosition u.1 +
            fkIsingSquareDirectionComplexStep d‖ := by rw [hvEq]
      _ ≤ ‖fkIsingSquareSitePosition u.1‖ +
          ‖fkIsingSquareDirectionComplexStep d‖ := norm_add_le _ _
      _ = ‖fkIsingSquareSitePosition u.1‖ + 1 := by rw [hstep]
      _ ≤ 2 * (m : Real) + 1 := by linarith
  have hcarrier :
      fkIsingSquareWiredCarrierPosition n (by omega)
          (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p) =
        (fkIsingSquareSitePosition u.1 + fkIsingSquareSitePosition v.1) / 2 := by
    change (fkIsingSquareSitePosition
        (fkIsingSquareOrientedEdge n
          (fkIsingSquareRadialPatchEdge n m hm i j)).tail.1 +
      fkIsingSquareSitePosition
        (fkIsingSquareOrientedEdge n
          (fkIsingSquareRadialPatchEdge n m hm i j)).head.1) / 2 = _
    rw [fkIsingSquareRadialPatchEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    exact congrArg (fun z : Complex ↦ z / 2)
      (fkIsingSquareDirectionEdgeOrientation_position_sum n u d _)
  rw [hcarrier]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : Real) < 1 / (m : Real))]
  calc
    (1 / (m : Real)) *
        ‖(fkIsingSquareSitePosition u.1 + fkIsingSquareSitePosition v.1) / 2‖ ≤
      (1 / (m : Real)) *
        ((‖fkIsingSquareSitePosition u.1‖ +
          ‖fkIsingSquareSitePosition v.1‖) / 2) := by
      gcongr
      rw [norm_div]
      norm_num
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / (m : Real)) *
        ((2 * (m : Real) + (2 * (m : Real) + 1)) / 2) := by
      gcongr
    _ ≤ 3 := by
      have hmpos : (0 : Real) < m := by positivity
      have hmone : (1 : Real) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      field_simp
      nlinarith




noncomputable def fkIsingExpandingSquareRadialSupport (k : Nat) :
    Finset (fkIsingExpandingSquareCaratheodoryApproximation.M k) := by
  classical
  by_cases hk : k = 0
  · exact {.source}
  · let n := fkIsingExpandingSquareSide k
    let m := k + 1
    let R := k / 2
    have hm : m ≤ n := by simp [m, n, fkIsingExpandingSquareSide]; nlinarith
    have hfit : 0 + R + 1 < m := by simp [R, m]; omega
    exact Finset.univ.map
      (fkIsingSquareRadialPatchWindowCarrierEmbedding
        n m 0 0 R hm hfit hfit)

theorem fkIsingExpandingSquareRadialSupport_nonempty (k : Nat) :
    (fkIsingExpandingSquareRadialSupport k).Nonempty := by
  classical
  by_cases hk : k = 0
  · simp [fkIsingExpandingSquareRadialSupport, hk]
  · simp [fkIsingExpandingSquareRadialSupport, hk]



theorem fkIsingExpandingSquareRadialSupport_mem_closedBall
    (k : Nat) (a : fkIsingExpandingSquareCaratheodoryApproximation.M k)
    (hk : k ≠ 0)
    (ha : a ∈ fkIsingExpandingSquareRadialSupport k) :
    dist (fkIsingExpandingSquareCaratheodoryApproximation.medialEmbedding k a)
      0 ≤ 4 := by
  classical
  let n := fkIsingExpandingSquareSide k
  let m := k + 1
  let R := k / 2
  have hm : m ≤ n := by simp [m, n, fkIsingExpandingSquareSide]; nlinarith
  have hm2 : 2 ≤ m := by simp [m]; omega
  have hfit : 0 + R + 1 < m := by simp [R, m]; omega
  rw [fkIsingExpandingSquareRadialSupport] at ha
  simp only [hk, ↓reduceDIte] at ha
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_map.mp ha
  have hbase := fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le
    n m 0 0 R hm hm2 hfit hfit p
  have hnear := fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    n (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
    (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p)
  change dist (fkIsingSquareWiredPerturbedCarrierPosition
      n (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
      (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p)) 0 ≤ 4
  rw [dist_zero_right]
  apply le_of_lt
  calc
      ‖fkIsingSquareWiredPerturbedCarrierPosition
          n (fkIsingExpandingSquareSide_pos k)
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
          (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p)‖ ≤
        ‖((fkIsingExpandingSquareScale k : Real) : Complex) *
          fkIsingSquareWiredCarrierPosition n (fkIsingExpandingSquareSide_pos k)
            (fkIsingSquareRadialPatchWindowCarrier
              n m 0 0 R hm hfit hfit p)‖ +
          dist (fkIsingSquareWiredPerturbedCarrierPosition
            n (fkIsingExpandingSquareSide_pos k)
            (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
            (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p))
            (((fkIsingExpandingSquareScale k : Real) : Complex) *
              fkIsingSquareWiredCarrierPosition n
                (fkIsingExpandingSquareSide_pos k)
                (fkIsingSquareRadialPatchWindowCarrier
                  n m 0 0 R hm hfit hfit p)) := by
        simpa [dist_eq_norm] using
          (norm_le_norm_add_norm_sub'
            (fkIsingSquareWiredPerturbedCarrierPosition
              n (fkIsingExpandingSquareSide_pos k)
              (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
              (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p))
            (((fkIsingExpandingSquareScale k : Real) : Complex) *
              fkIsingSquareWiredCarrierPosition n
                (fkIsingExpandingSquareSide_pos k)
                (fkIsingSquareRadialPatchWindowCarrier
                  n m 0 0 R hm hfit hfit p)))
      _ < 3 + fkIsingExpandingSquareScale k / 10 :=
        add_lt_add_of_le_of_lt (by simpa [m, fkIsingExpandingSquareScale] using hbase)
          hnear
      _ < 4 := by
        have hs : fkIsingExpandingSquareScale k ≤ 1 := by
          rw [fkIsingExpandingSquareScale]
          rw [one_div]
          apply inv_le_one_of_one_le₀
          norm_num
        linarith



theorem fkIsingExpandingSquareRadialSupport_hasEventualCompactWindowDiameter :
    FKIsingCaratheodoryApproximation.HasEventualCompactWindowDiameter
      fkIsingExpandingSquareCaratheodoryApproximation
      fkIsingExpandingSquareRadialSupport := by
  apply FKIsingCaratheodoryApproximation.hasEventualCompactWindowDiameter_of_commonBall
  intro K hK _hKU
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  let B := max 4 (C + 4)
  refine ⟨0, B, (show (0 : Real) ≤ 4 by norm_num).trans
    (le_max_left 4 (C + 4)), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : k ≠ 0 := by omega
  have hscale : fkIsingExpandingSquareScale k ≤ 1 := by
    rw [fkIsingExpandingSquareScale, one_div]
    apply inv_le_one_of_one_le₀
    norm_num
  have hmesh : fkIsingExpandingSquareMesh k ≤ 4 := by
    rw [fkIsingExpandingSquareMesh]
    nlinarith
  constructor
  · intro a ha
    exact (fkIsingExpandingSquareRadialSupport_mem_closedBall k a hk0 ha).trans
      (le_max_left 4 (C + 4))
  · intro e he
    obtain ⟨z, hzK, hznear⟩ := he
    have hzC : dist z 0 ≤ C := hC hzK
    calc
      dist (fkIsingExpandingSquareCaratheodoryApproximation.medialEmbedding k e)
          0 ≤
        dist (fkIsingExpandingSquareCaratheodoryApproximation.medialEmbedding k e)
            z + dist z 0 := dist_triangle _ _ _
      _ ≤ fkIsingExpandingSquareMesh k + C :=
        add_le_add (by simpa [dist_comm] using hznear) hzC
      _ ≤ 4 + C := by simpa [add_comm] using add_le_add_right hmesh C
      _ = C + 4 := by ring
      _ ≤ B := le_max_right 4 (C + 4)

end

end StatMech.Universality
