/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Code.FrontierA.Z2GaugeInfiniteVolume

open Finset
open scoped BigOperators symmDiff

namespace StatMech.FrontierA

noncomputable section



theorem gaugeWilsonExpectation_prod_boundary_le_biUnion
    {I E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P] [DecidableEq I]
    (incidence : P -> Finset E) (K : P -> Real) (hK : forall p, 0 < K p)
    (S : Finset I) (D : I -> Finset P)
    (hdisj : forall i, i ∈ S -> forall j, j ∈ S -> i ≠ j ->
      Disjoint (D i) (D j)) :
    (∏ i ∈ S, gaugeWilsonExpectation incidence K
        (gaugeSurfaceBoundary incidence (D i))) <=
      gaugeWilsonExpectation incidence K
        (gaugeSurfaceBoundary incidence (S.biUnion D)) := by
  induction S using Finset.induction_on with
  | empty =>
      simp [gaugeSurfaceBoundary, plaquetteIncidenceCount,
        gaugeWilsonExpectation_empty]
  | @insert i S hi ih =>
      have hrest : forall j, j ∈ S -> forall k, k ∈ S -> j ≠ k ->
          Disjoint (D j) (D k) := by
        intro j hj k hk hjk
        exact hdisj j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk
      have hsurface : Disjoint (D i) (S.biUnion D) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj i (Finset.mem_insert_self i S) j
          (Finset.mem_insert_of_mem hj) (by aesop)
      have hi_nonneg : 0 <= gaugeWilsonExpectation incidence K
          (gaugeSurfaceBoundary incidence (D i)) :=
        (gaugeWilsonExpectation_mem_Icc incidence K hK _).1
      have hunion_nonneg : 0 <= gaugeWilsonExpectation incidence K
          (gaugeSurfaceBoundary incidence (S.biUnion D)) :=
        (gaugeWilsonExpectation_mem_Icc incidence K hK _).1
      have hmul := gaugeWilsonExpectation_mul_le_symmDiff incidence K
        (fun p => (hK p).le)
        (gaugeSurfaceBoundary incidence (D i))
        (gaugeSurfaceBoundary incidence (S.biUnion D))
      rw [Finset.prod_insert hi, Finset.biUnion_insert]
      calc
        gaugeWilsonExpectation incidence K
              (gaugeSurfaceBoundary incidence (D i)) *
            ∏ j ∈ S, gaugeWilsonExpectation incidence K
              (gaugeSurfaceBoundary incidence (D j)) <=
            gaugeWilsonExpectation incidence K
                (gaugeSurfaceBoundary incidence (D i)) *
              gaugeWilsonExpectation incidence K
                (gaugeSurfaceBoundary incidence (S.biUnion D)) :=
          mul_le_mul_of_nonneg_left (ih hrest) hi_nonneg
        _ <= gaugeWilsonExpectation incidence K
            (gaugeSurfaceBoundary incidence (D i) ∆
              gaugeSurfaceBoundary incidence (S.biUnion D)) := hmul
        _ = gaugeWilsonExpectation incidence K
            (gaugeSurfaceBoundary incidence (D i ∪ S.biUnion D)) := by
          rw [gaugeSurfaceBoundary_union_of_disjoint incidence hsurface]

private def tripleTileSide (n : Nat) : Nat := 2 * n + 1

private def tripleTiledSide (n : Nat) : Nat := 2 * (3 * n + 1) + 1

private def tripleCentralHeight (n : Nat) : Nat := 3 * n + 2

private def tripleCentralHeightFin (n : Nat) : Fin (tripleTiledSide n + 1) :=
  ⟨tripleCentralHeight n, by
    simp only [tripleCentralHeight, tripleTiledSide, tripleTileSide]
    omega⟩

private theorem tripleTile_fit (n : Nat) (q : Fin 3) :
    q.val * tripleTileSide n + tripleTileSide n <= tripleTiledSide n := by
  calc
    q.val * tripleTileSide n + tripleTileSide n =
        (q.val + 1) * tripleTileSide n := by simp [Nat.add_mul]
    _ <= 3 * tripleTileSide n :=
      Nat.mul_le_mul_right (tripleTileSide n) (by omega)
    _ = tripleTiledSide n := by
      unfold tripleTiledSide tripleTileSide
      ring

private theorem tripleTile_height_fit (n : Nat) :
    tripleCentralHeight n + tripleTileSide n <= tripleTiledSide n := by
  simp [tripleCentralHeight, tripleTileSide, tripleTiledSide]
  omega



private def tripleTileSheet (n : Nat) (q : Fin 3 × Fin 3) :
    Finset (CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n)
      (tripleTiledSide n)) :=
  let L := tripleTileSide n
  (cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1))).map
    (cubicalPlaquetteChart (A := tripleTiledSide n)
      (B := tripleTiledSide n) (C := tripleTiledSide n)
      (q.1.val * L) (q.2.val * L) (tripleCentralHeight n)
      (tripleTile_fit n q.1) (tripleTile_fit n q.2)
      (tripleTile_height_fit n))

private def tripleTileLoop (n : Nat) (q : Fin 3 × Fin 3) :
    Finset (CubicalEdge (tripleTiledSide n) (tripleTiledSide n)
      (tripleTiledSide n)) :=
  let L := tripleTileSide n
  (cubicalXYLoop (a := L) (b := L) (c := L) (0 : Fin (L + 1))).map
    (cubicalEdgeChart (A := tripleTiledSide n)
      (B := tripleTiledSide n) (C := tripleTiledSide n)
      (q.1.val * L) (q.2.val * L) (tripleCentralHeight n)
      (tripleTile_fit n q.1) (tripleTile_fit n q.2)
      (tripleTile_height_fit n))

private theorem tripleTileLoop_eq_boundary (n : Nat) (q : Fin 3 × Fin 3) :
    tripleTileLoop n q =
      gaugeSurfaceBoundary cubicalPlaquetteIncidence (tripleTileSheet n q) := by
  let L := tripleTileSide n
  let e := cubicalEdgeChart (a := L) (b := L) (c := L)
    (A := tripleTiledSide n) (B := tripleTiledSide n)
    (C := tripleTiledSide n)
    (q.1.val * L) (q.2.val * L) (tripleCentralHeight n)
    (tripleTile_fit n q.1) (tripleTile_fit n q.2)
    (tripleTile_height_fit n)
  let p := cubicalPlaquetteChart (a := L) (b := L) (c := L)
    (A := tripleTiledSide n) (B := tripleTiledSide n)
    (C := tripleTiledSide n)
    (q.1.val * L) (q.2.val * L) (tripleCentralHeight n)
    (tripleTile_fit n q.1) (tripleTile_fit n q.2)
    (tripleTile_height_fit n)
  change (cubicalXYLoop (a := L) (b := L) (c := L)
      (0 : Fin (L + 1))).map e =
    gaugeSurfaceBoundary cubicalPlaquetteIncidence
      ((cubicalXYSheet (a := L) (b := L) (c := L)
        (0 : Fin (L + 1))).map p)
  rw [gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
    cubicalPlaquetteIncidence e p]
  · rfl
  · exact cubicalPlaquetteIncidence_chart _ _ _ _ _ _

private theorem tripleTileSheet_pairwise_disjoint (n : Nat) :
    forall q, q ∈ (Finset.univ : Finset (Fin 3 × Fin 3)) ->
      forall r, r ∈ (Finset.univ : Finset (Fin 3 × Fin 3)) -> q ≠ r ->
        Disjoint (tripleTileSheet n q) (tripleTileSheet n r) := by
  intro q _ r _ hqr
  rw [Finset.disjoint_left]
  intro p hpq hpr
  cases p with
  | xy x y z =>
      simp only [tripleTileSheet, cubicalXYSheet, Finset.mem_map,
        Finset.mem_image, Finset.mem_univ, true_and] at hpq hpr
      obtain ⟨_, ⟨ijq, _, rfl⟩, hpq⟩ := hpq
      obtain ⟨_, ⟨ijr, _, rfl⟩, hpr⟩ := hpr
      change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z at hpq hpr
      rw [CubicalPlaquette.xy.injEq] at hpq hpr
      have hx : q.1.val = r.1.val := by
        have h := congrArg (fun t : Fin (tripleTiledSide n) => t.val)
          (hpq.1.trans hpr.1.symm)
        simp only [finOffsetEmbedding_val] at h
        have hL : 0 < tripleTileSide n := by simp [tripleTileSide]
        have hiq := ijq.1.isLt
        have hir := ijr.1.isLt
        nlinarith
      have hy : q.2.val = r.2.val := by
        have h := congrArg (fun t : Fin (tripleTiledSide n) => t.val)
          (hpq.2.1.trans hpr.2.1.symm)
        simp only [finOffsetEmbedding_val] at h
        have hL : 0 < tripleTileSide n := by simp [tripleTileSide]
        have hiq := ijq.2.isLt
        have hir := ijr.2.isLt
        nlinarith
      apply hqr
      apply Prod.ext <;> apply Fin.ext
      · exact hx
      · exact hy
  | xz x y z =>
      simp [tripleTileSheet, cubicalXYSheet, cubicalPlaquetteChart] at hpq
  | yz x y z =>
      simp [tripleTileSheet, cubicalXYSheet, cubicalPlaquetteChart] at hpq

private theorem tripleTileSheet_biUnion (n : Nat) :
    (Finset.univ : Finset (Fin 3 × Fin 3)).biUnion (tripleTileSheet n) =
      cubicalXYSheet (a := tripleTiledSide n) (b := tripleTiledSide n)
        (c := tripleTiledSide n) (tripleCentralHeightFin n) := by
  ext p
  cases p with
  | xy x y z =>
      constructor
      · intro hp
        simp only [Finset.mem_biUnion] at hp
        obtain ⟨q, _, hq⟩ := hp
        simp only [tripleTileSheet, cubicalXYSheet, Finset.mem_map,
          Finset.mem_image, Finset.mem_univ, true_and] at hq
        obtain ⟨_, ⟨ij, _, rfl⟩, hpq⟩ := hq
        change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z at hpq
        rw [CubicalPlaquette.xy.injEq] at hpq
        simp only [cubicalXYSheet, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨(x, y), ?_⟩
        simpa [tripleCentralHeightFin] using hpq.2.2
      · intro hp
        simp only [cubicalXYSheet, Finset.mem_image, Finset.mem_univ,
          true_and] at hp
        obtain ⟨xy, hxy⟩ := hp
        have hz : z = tripleCentralHeightFin n :=
          (CubicalPlaquette.xy.inj hxy).2.2.symm
        let L := tripleTileSide n
        have hL : 0 < L := by simp [L, tripleTileSide]
        let qx : Fin 3 := ⟨x.val / L, by
          have hx := x.isLt
          have hside : tripleTiledSide n = 3 * L := by
            dsimp [L, tripleTiledSide, tripleTileSide]
            ring
          have hx' : x.val < 3 * L := hx.trans_le hside.le
          exact (Nat.div_lt_iff_lt_mul hL).2 (by simpa [mul_comm] using hx')⟩
        let qy : Fin 3 := ⟨y.val / L, by
          have hy := y.isLt
          have hside : tripleTiledSide n = 3 * L := by
            dsimp [L, tripleTiledSide, tripleTileSide]
            ring
          have hy' : y.val < 3 * L := hy.trans_le hside.le
          exact (Nat.div_lt_iff_lt_mul hL).2 (by simpa [mul_comm] using hy')⟩
        let ix : Fin L := ⟨x.val % L, Nat.mod_lt _ hL⟩
        let iy : Fin L := ⟨y.val % L, Nat.mod_lt _ hL⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨(qx, qy), Finset.mem_univ _, ?_⟩
        apply Finset.mem_map.mpr
        refine ⟨CubicalPlaquette.xy ix iy (0 : Fin (L + 1)), ?_, ?_⟩
        · apply Finset.mem_image.mpr
          exact ⟨(ix, iy), Finset.mem_univ _, rfl⟩
        · change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z
          rw [CubicalPlaquette.xy.injEq]
          constructor
          · apply Fin.ext
            simp only [finOffsetEmbedding_val]
            simpa [qx, ix, Nat.mul_comm] using Nat.div_add_mod x.val L
          constructor
          · apply Fin.ext
            simp only [finOffsetEmbedding_val]
            simpa [qy, iy, Nat.mul_comm] using Nat.div_add_mod y.val L
          · apply Fin.ext
            exact congrArg Fin.val hz.symm
  | xz x y z =>
      simp [tripleTileSheet, cubicalXYSheet, cubicalPlaquetteChart]
  | yz x y z =>
      simp [tripleTileSheet, cubicalXYSheet, cubicalPlaquetteChart]



theorem oddCubicalWilson_nineTile_le_central
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    (gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (tripleTileSide n) (tripleTileSide n)
          (tripleTileSide n) => beta)
        (cubicalXYLoop (a := tripleTileSide n) (b := tripleTileSide n)
          (c := tripleTileSide n) (0 : Fin (tripleTileSide n + 1)))) ^ 9 <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n)
          (tripleTiledSide n) => beta)
        (cubicalXYLoop (a := tripleTiledSide n) (b := tripleTiledSide n)
          (c := tripleTiledSide n) (tripleCentralHeightFin n)) := by
  let smallW := gaugeWilsonExpectation cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette (tripleTileSide n) (tripleTileSide n)
      (tripleTileSide n) => beta)
    (cubicalXYLoop (a := tripleTileSide n) (b := tripleTileSide n)
      (c := tripleTileSide n) (0 : Fin (tripleTileSide n + 1)))
  let tileW : Fin 3 × Fin 3 -> Real := fun q =>
    gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n)
        (tripleTiledSide n) => beta) (tripleTileLoop n q)
  have htile (q : Fin 3 × Fin 3) : smallW <= tileW q := by
    dsimp [smallW, tileW, tripleTileLoop]
    exact cubicalXYWilsonExpectation_le_chart
      (q.1.val * tripleTileSide n) (q.2.val * tripleTileSide n)
      (tripleCentralHeight n)
      (tripleTile_fit n q.1) (tripleTile_fit n q.2)
      (tripleTile_height_fit n)
      hbeta.le (0 : Fin (tripleTileSide n + 1))
  have hsmall_nonneg : 0 <= smallW :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (tripleTileSide n) (tripleTileSide n)
        (tripleTileSide n) => beta) (fun _ => hbeta) _).1
  have hprod : smallW ^ 9 <= ∏ q : Fin 3 × Fin 3, tileW q := by
    have hp := Finset.prod_le_prod
      (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (f := fun _ => smallW) (g := tileW)
      (fun _ _ => hsmall_nonneg) (fun q _ => htile q)
    simpa using hp
  have hglue := gaugeWilsonExpectation_prod_boundary_le_biUnion
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n)
      (tripleTiledSide n) => beta) (fun _ => hbeta)
    (Finset.univ : Finset (Fin 3 × Fin 3)) (tripleTileSheet n)
    (tripleTileSheet_pairwise_disjoint n)
  simp_rw [← tripleTileLoop_eq_boundary] at hglue
  rw [tripleTileSheet_biUnion] at hglue
  exact hprod.trans (by simpa [smallW, tileW] using hglue)

set_option maxHeartbeats 2000000 in



theorem oddCubicalCentralSheetFreeEnergy_triple_le_nine_lower
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    oddCubicalCentralSheetFreeEnergy beta (3 * n + 1) <=
      9 * oddCubicalLowerSheetFreeEnergy beta n := by
  let K := gaugeCriticalCoupling beta
  have hK : 0 < K := gaugeCriticalCoupling_pos hbeta
  have hw := oddCubicalWilson_nineTile_le_central hK n
  have hsmall : 0 < gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (tripleTileSide n) (tripleTileSide n)
        (tripleTileSide n) => K)
      (cubicalXYLoop (a := tripleTileSide n) (b := tripleTileSide n)
        (c := tripleTileSide n) (0 : Fin (tripleTileSide n + 1))) := by
    apply (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence (fun _ => K) (fun _ => hK) _).2
    exact ⟨cubicalXYSheet (0 : Fin (tripleTileSide n + 1)),
      cubicalXYSheet_hasWilsonBoundary _⟩
  have hbig : 0 < gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n)
        (tripleTiledSide n) => K)
      (cubicalXYLoop (a := tripleTiledSide n) (b := tripleTiledSide n)
        (c := tripleTiledSide n) (tripleCentralHeightFin n)) := by
    apply (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence (fun _ => K) (fun _ => hK) _).2
    exact ⟨cubicalXYSheet (tripleCentralHeightFin n),
      cubicalXYSheet_hasWilsonBoundary _⟩
  have hlog := Real.log_le_log (pow_pos hsmall 9) hw
  rw [Real.log_pow] at hlog
  have hsmallDFE := neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
    (a := tripleTileSide n) (b := tripleTileSide n) (c := tripleTileSide n)
    (by simp [tripleTileSide]) (by simp [tripleTileSide])
    (by simp [tripleTileSide]) (0 : Fin (tripleTileSide n + 1))
    (fun _ => K) (fun _ => hK)
  have hbigDFE := neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
    (a := tripleTiledSide n) (b := tripleTiledSide n)
    (c := tripleTiledSide n) (by simp [tripleTiledSide, tripleTileSide])
    (by simp [tripleTiledSide, tripleTileSide])
    (by simp [tripleTiledSide, tripleTileSide])
    (tripleCentralHeightFin n) (fun _ => K) (fun _ => hK)
  dsimp [K] at hsmallDFE hbigDFE
  simp_rw [gaugeDualCoupling_gaugeCriticalCoupling hbeta] at hsmallDFE hbigDFE
  have hcentral : oddCubicalCentralSheetFreeEnergy beta (3 * n + 1) =
      -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n)
          (tripleTiledSide n) => gaugeCriticalCoupling beta)
        (cubicalXYLoop (tripleCentralHeightFin n))) := by
    unfold oddCubicalCentralSheetFreeEnergy
    dsimp
    exact hbigDFE.symm
  have hlower : oddCubicalLowerSheetFreeEnergy beta n =
      -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (tripleTileSide n) (tripleTileSide n)
          (tripleTileSide n) => gaugeCriticalCoupling beta)
        (cubicalXYLoop (0 : Fin (tripleTileSide n + 1)))) := by
    simpa [oddCubicalLowerSheetFreeEnergy, tripleTileSide] using hsmallDFE.symm
  rw [hcentral, hlower]
  dsimp [K] at hlog
  linarith



theorem centralCubicalIsingDisorderDensity_triple_le_odd
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    centralCubicalIsingDisorderDensity beta (3 * n + 1) <=
      oddCubicalIsingDisorderDensity beta n := by
  rw [centralCubicalIsingDisorderDensity_eq_centralSheetFreeEnergy_div,
    oddCubicalIsingDisorderDensity_eq_lowerSheetFreeEnergy_div hbeta]
  have hraw := oddCubicalCentralSheetFreeEnergy_triple_le_nine_lower hbeta n
  have hL : (0 : Real) < (2 * n + 1 : Nat) := by positivity
  rw [div_le_div_iff₀ (by positivity :
    (0 : Real) < (((2 * (3 * n + 1) + 1 : Nat) : Real) ^ 2))
    (sq_pos_of_pos hL)]
  push_cast
  nlinarith




theorem rectangularIsingSurfaceTension_pos
    {beta : Real} (hcritical : StatMech.Ising.betaC 3 < beta) :
    0 < rectangularIsingSurfaceTension beta := by
  have hbetaC : 0 < StatMech.Ising.betaC 3 := by
    have hbdd := StatMech.Sharpness.tildeBetaCIsingSet_bddAbove
      (d := 3) (by norm_num)
    have hcrit := StatMech.Sharpness.tildeBetaCIsing_pos
      (d := 3) (by norm_num)
    have hsqrt : forall gamma, StatMech.Sharpness.tildeBetaCIsing 3 <= gamma ->
        Real.sqrt (1 - (StatMech.Sharpness.tildeBetaCIsing 3 / gamma) ^ 2) <=
          StatMech.Ising.magnetization 3 gamma := fun gamma hgamma =>
      StatMech.Sharpness.sct_magnetization_meanfield_lower_bound_integrated
        3 hbdd hcrit hgamma
    rw [StatMech.Sharpness.bc_eq_ising_of_sqrt_and_susceptibility
      (d := 3) (by norm_num) hsqrt]
    exact hcrit
  have hsharp :=
    (StatMech.Sharpness.ising_sharpness_unconditional
      (d := 3) (by norm_num)).1
  let a : Real := (StatMech.Ising.betaC 3 + beta) / 2
  let c : Real :=
    2 * (Real.sqrt (1 - (StatMech.Ising.betaC 3 / a) ^ 2)) ^ 2 * (beta - a)
  have ha : StatMech.Ising.betaC 3 < a := by dsimp [a]; linarith
  have hab : a < beta := by dsimp [a]; linarith
  have ha0 : 0 < a := hbetaC.trans ha
  have hratio0 : 0 <= StatMech.Ising.betaC 3 / a :=
    div_nonneg hbetaC.le ha0.le
  have hratio1 : StatMech.Ising.betaC 3 / a < 1 := (div_lt_one ha0).2 ha
  have hrad : 0 < 1 - (StatMech.Ising.betaC 3 / a) ^ 2 := by nlinarith
  have hc : 0 < c := by
    dsimp [c]
    rw [Real.sq_sqrt hrad.le]
    positivity
  have hlower : forall n, c <= oddCubicalIsingDisorderDensity beta n := by
    intro n
    calc
      c <= standardCubicInterfaceDensity beta (3 * n + 1) := by
        dsimp [c]
        exact standardCubicInterfaceDensity_ge_meanfield_increment
          hbetaC hsharp ha hab (3 * n + 1) (by omega)
      _ = centralCubicalIsingDisorderDensity beta (3 * n + 1) :=
        standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity
          beta (3 * n + 1) (by omega)
      _ <= oddCubicalIsingDisorderDensity beta n :=
        centralCubicalIsingDisorderDensity_triple_le_odd
          (hbetaC.trans hcritical) n
  have hlim := oddCubicalIsingDisorderDensity_tendsto
    (hbetaC.trans hcritical)
  have hcle : c <= rectangularIsingSurfaceTension beta :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hlower)
  exact hc.trans_le hcle

end

end StatMech.FrontierA
