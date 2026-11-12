/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation
import Code.FrontierA.IsingSurfaceTensionSheetTiling
import Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
import Code.FrontierA.Z2GaugeSurfaceTensionIdentification











open Finset Filter Topology
open scoped BigOperators symmDiff

namespace StatMech.FrontierA

noncomputable section

def cubicalInteriorBlockSide (L p k : Nat) : Nat :=
  p + k * L + p

def cubicalInteriorBlockHeight (L p k : Nat) :
    Fin (cubicalInteriorBlockSide L p k + 1) :=
  ⟨p, by simp [cubicalInteriorBlockSide]⟩

private theorem cubicalInteriorBlockTile_fit
    (L p k : Nat) (q : Fin k) :
    p + q.val * L + L <= cubicalInteriorBlockSide L p k := by
  have hq : q.val + 1 <= k := Nat.succ_le_iff.mpr q.isLt
  have hmul : (q.val + 1) * L <= k * L := Nat.mul_le_mul_right L hq
  calc
    p + q.val * L + L = p + (q.val + 1) * L := by ring
    _ <= p + k * L := Nat.add_le_add_left hmul p
    _ <= cubicalInteriorBlockSide L p k := by
      simp [cubicalInteriorBlockSide]

def cubicalInteriorBlockTileSheet
    (L p k : Nat) (q : Fin k × Fin k) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYSheet (a := L) (b := L) (c := 0) (0 : Fin 1)).map
    (cubicalPlaquetteChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))

def cubicalInteriorBlockTileLoop
    (L p k : Nat) (q : Fin k × Fin k) :
    Finset (CubicalEdge
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYLoop (a := L) (b := L) (c := 0) (0 : Fin 1)).map
    (cubicalEdgeChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))

theorem cubicalInteriorBlockTileLoop_eq_boundary
    (L p k : Nat) (q : Fin k × Fin k) :
    cubicalInteriorBlockTileLoop L p k q =
      gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalInteriorBlockTileSheet L p k q) := by
  unfold cubicalInteriorBlockTileLoop cubicalInteriorBlockTileSheet
    cubicalXYLoop
  exact (gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
    cubicalPlaquetteIncidence
    (cubicalEdgeChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))
    (cubicalPlaquetteChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))
    (fun plaquette => cubicalPlaquetteIncidence_chart
      (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]) plaquette)
    (cubicalXYSheet (a := L) (b := L) (c := 0) (0 : Fin 1))).symm

theorem cubicalInteriorBlockTileSheet_pairwise_disjoint
    (L p k : Nat) (hL : 0 < L) :
    ∀ q : Fin k × Fin k, q ∈ (Finset.univ : Finset (Fin k × Fin k)) ->
      ∀ r : Fin k × Fin k, r ∈ (Finset.univ : Finset (Fin k × Fin k)) ->
        q ≠ r -> Disjoint (cubicalInteriorBlockTileSheet L p k q)
          (cubicalInteriorBlockTileSheet L p k r) := by
  intro q _ r _ hqr
  rw [Finset.disjoint_left]
  intro plaquette hpq hpr
  cases plaquette with
  | xy x y z =>
      simp only [cubicalInteriorBlockTileSheet, cubicalXYSheet,
        Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hpq hpr
      obtain ⟨_, ⟨ijq, _, rfl⟩, hpq⟩ := hpq
      obtain ⟨_, ⟨ijr, _, rfl⟩, hpr⟩ := hpr
      change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z at hpq hpr
      rw [CubicalPlaquette.xy.injEq] at hpq hpr
      have hx : q.1.val = r.1.val := by
        have h := congrArg Fin.val (hpq.1.trans hpr.1.symm)
        simp only [finOffsetEmbedding_val] at h
        have h' : q.1.val * L + ijq.1.val =
            r.1.val * L + ijr.1.val := by omega
        have hd := congrArg (fun z : Nat => z / L) h'
        simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div hL,
          Nat.div_eq_of_lt ijq.1.isLt,
          Nat.div_eq_of_lt ijr.1.isLt] using hd
      have hy : q.2.val = r.2.val := by
        have h := congrArg Fin.val (hpq.2.1.trans hpr.2.1.symm)
        simp only [finOffsetEmbedding_val] at h
        have h' : q.2.val * L + ijq.2.val =
            r.2.val * L + ijr.2.val := by omega
        have hd := congrArg (fun z : Nat => z / L) h'
        simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div hL,
          Nat.div_eq_of_lt ijq.2.isLt,
          Nat.div_eq_of_lt ijr.2.isLt] using hd
      apply hqr
      apply Prod.ext <;> apply Fin.ext
      · exact hx
      · exact hy
  | xz x y z =>
      simp [cubicalInteriorBlockTileSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq
  | yz x y z =>
      simp [cubicalInteriorBlockTileSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq

def cubicalInteriorBlockCentralSheet (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYSheet (a := k * L) (b := k * L) (c := 0) (0 : Fin 1)).map
    (cubicalPlaquetteChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))

def cubicalInteriorBlockCentralLoop (L p k : Nat) :
    Finset (CubicalEdge
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYLoop (a := k * L) (b := k * L) (c := 0) (0 : Fin 1)).map
    (cubicalEdgeChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))

theorem cubicalInteriorBlockCentralLoop_eq_boundary
    (L p k : Nat) :
    cubicalInteriorBlockCentralLoop L p k =
      gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalInteriorBlockCentralSheet L p k) := by
  unfold cubicalInteriorBlockCentralLoop cubicalInteriorBlockCentralSheet
    cubicalXYLoop
  exact (gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
    cubicalPlaquetteIncidence
    (cubicalEdgeChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))
    (cubicalPlaquetteChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))
    (fun plaquette => cubicalPlaquetteIncidence_chart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]) plaquette)
    (cubicalXYSheet (a := k * L) (b := k * L) (c := 0)
      (0 : Fin 1))).symm

theorem cubicalInteriorBlockTileSheet_biUnion
    (L p k : Nat) (hL : 0 < L) :
    (Finset.univ : Finset (Fin k × Fin k)).biUnion
        (cubicalInteriorBlockTileSheet L p k) =
      cubicalInteriorBlockCentralSheet L p k := by
  ext plaquette
  cases plaquette with
  | xy x y z =>
      constructor
      · intro hp
        simp only [Finset.mem_biUnion] at hp
        obtain ⟨q, _, hq⟩ := hp
        simp only [cubicalInteriorBlockTileSheet, cubicalXYSheet,
          Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hq
        obtain ⟨_, ⟨ij, _, rfl⟩, hpq⟩ := hq
        simp only [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
          Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and]
        let ci : Fin (k * L) := ⟨q.1.val * L + ij.1.val, by
          have hq' : q.1.val + 1 <= k := Nat.succ_le_iff.mpr q.1.isLt
          have hmul := Nat.mul_le_mul_right L hq'
          calc
            q.1.val * L + ij.1.val < q.1.val * L + L :=
              Nat.add_lt_add_left ij.1.isLt _
            _ = (q.1.val + 1) * L := by ring
            _ <= k * L := hmul⟩
        let cj : Fin (k * L) := ⟨q.2.val * L + ij.2.val, by
          have hq' : q.2.val + 1 <= k := Nat.succ_le_iff.mpr q.2.isLt
          have hmul := Nat.mul_le_mul_right L hq'
          calc
            q.2.val * L + ij.2.val < q.2.val * L + L :=
              Nat.add_lt_add_left ij.2.isLt _
            _ = (q.2.val + 1) * L := by ring
            _ <= k * L := hmul⟩
        refine ⟨CubicalPlaquette.xy ci cj (0 : Fin 1), ?_, ?_⟩
        · exact ⟨(ci, cj), rfl⟩
        · change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z
          have hpqcoord := CubicalPlaquette.xy.inj hpq
          rw [CubicalPlaquette.xy.injEq]
          constructor
          · apply Fin.ext
            calc
              (finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) ci).val =
                  p + (q.1.val * L + ij.1.val) := by rfl
              _ = (finOffsetEmbedding (p + q.1.val * L)
                  (cubicalInteriorBlockTile_fit L p k q.1) ij.1).val := by
                    simp only [finOffsetEmbedding_val]
                    omega
              _ = x.val := congrArg Fin.val hpqcoord.1
          constructor
          · apply Fin.ext
            calc
              (finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) cj).val =
                  p + (q.2.val * L + ij.2.val) := by rfl
              _ = (finOffsetEmbedding (p + q.2.val * L)
                  (cubicalInteriorBlockTile_fit L p k q.2) ij.2).val := by
                    simp only [finOffsetEmbedding_val]
                    omega
              _ = y.val := congrArg Fin.val hpqcoord.2.1
          · exact hpqcoord.2.2
      · intro hp
        simp only [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
          Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨_, ⟨ij, _, rfl⟩, hp⟩ := hp
        have hpcoord := CubicalPlaquette.xy.inj hp
        let qx : Fin k := ⟨ij.1.val / L, by
          apply (Nat.div_lt_iff_lt_mul hL).2
          simpa [Nat.mul_comm] using ij.1.isLt⟩
        let qy : Fin k := ⟨ij.2.val / L, by
          apply (Nat.div_lt_iff_lt_mul hL).2
          simpa [Nat.mul_comm] using ij.2.isLt⟩
        let ix : Fin L := ⟨ij.1.val % L, Nat.mod_lt _ hL⟩
        let iy : Fin L := ⟨ij.2.val % L, Nat.mod_lt _ hL⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨(qx, qy), Finset.mem_univ _, ?_⟩
        apply Finset.mem_map.mpr
        refine ⟨CubicalPlaquette.xy ix iy (0 : Fin 1), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨(ix, iy), Finset.mem_univ _, rfl⟩
        · change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy _ _ _
          rw [CubicalPlaquette.xy.injEq]
          constructor
          · apply Fin.ext
            simp only [finOffsetEmbedding_val]
            calc
              p + qx.val * L + ix.val = p + ij.1.val := by
                rw [show qx.val = ij.1.val / L by rfl,
                  show ix.val = ij.1.val % L by rfl]
                have hinner : (ij.1.val / L) * L + ij.1.val % L =
                    ij.1.val := by
                  simpa [Nat.mul_comm] using Nat.div_add_mod ij.1.val L
                omega
              _ = x.val := congrArg Fin.val hpcoord.1
          constructor
          · apply Fin.ext
            simp only [finOffsetEmbedding_val]
            calc
              p + qy.val * L + iy.val = p + ij.2.val := by
                rw [show qy.val = ij.2.val / L by rfl,
                  show iy.val = ij.2.val % L by rfl]
                have hinner : (ij.2.val / L) * L + ij.2.val % L =
                    ij.2.val := by
                  simpa [Nat.mul_comm] using Nat.div_add_mod ij.2.val L
                omega
              _ = y.val := congrArg Fin.val hpcoord.2.1
          · apply Fin.ext
            exact congrArg Fin.val hpcoord.2.2
  | xz x y z =>
      simp [cubicalInteriorBlockTileSheet,
        cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart]
  | yz x y z =>
      simp [cubicalInteriorBlockTileSheet,
        cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart]


theorem cubicalPaddedWilsonExpectation_pow_sq_le_interiorBlockCentral
    {K : Real} (hK : 0 < K) (L p k : Nat) (hL : 0 < L) :
    (cubicalPaddedWilsonExpectation K L L p p p p p p) ^ (k * k) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => K)
        (cubicalInteriorBlockCentralLoop L p k) := by
  let N := cubicalInteriorBlockSide L p k
  let smallW := cubicalPaddedWilsonExpectation K L L p p p p p p
  let tileW : Fin k × Fin k -> Real := fun q =>
    gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette N N N => K)
      (cubicalInteriorBlockTileLoop L p k q)
  have htile (q : Fin k × Fin k) : smallW <= tileW q := by
    let A := p + L + p
    let C := p + p
    let L0 := cubicalXYLoop (a := L) (b := L) (c := 0) (0 : Fin 1)
    let inner := cubicalEdgeChart p p p
      (a := L) (b := L) (c := 0) (A := A) (B := A) (C := C)
      (by dsimp [A]; omega) (by dsimp [A]; omega) (by dsimp [C]; omega)
    have hxOuter : q.1.val * L + A <= N := by
      have hq : q.1.val + 1 <= k := Nat.succ_le_iff.mpr q.1.isLt
      have hmul := Nat.mul_le_mul_right L hq
      dsimp [A, N, cubicalInteriorBlockSide]
      nlinarith
    have hyOuter : q.2.val * L + A <= N := by
      have hq : q.2.val + 1 <= k := Nat.succ_le_iff.mpr q.2.isLt
      have hmul := Nat.mul_le_mul_right L hq
      dsimp [A, N, cubicalInteriorBlockSide]
      nlinarith
    have hzOuter : 0 + C <= N := by
      dsimp [C, N, cubicalInteriorBlockSide]
      omega
    let outer := cubicalEdgeChart (q.1.val * L) (q.2.val * L) 0
      (a := A) (b := A) (c := C) (A := N) (B := N) (C := N)
      hxOuter hyOuter hzOuter
    let target := cubicalEdgeChart (p + q.1.val * L)
      (p + q.2.val * L) p
      (a := L) (b := L) (c := 0) (A := N) (B := N) (C := N)
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by dsimp [N, cubicalInteriorBlockSide]; omega)
    have hmap : (L0.map inner).map outer = L0.map target := by
      rw [Finset.map_map]
      congr 1
      ext edge
      simpa [inner, outer, target, A, C, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using
        (cubicalEdgeChart_comp_apply p p p
          (q.1.val * L) (q.2.val * L) 0
          (by dsimp [A]; omega) (by dsimp [A]; omega)
          (by dsimp [C]; omega) hxOuter hyOuter hzOuter edge)
    have h := cubicalWilsonExpectation_le_chart
      (a := A) (b := A) (c := C) (A := N) (B := N) (C := N)
      (q.1.val * L) (q.2.val * L) 0 hxOuter hyOuter hzOuter hK.le
      (L0.map inner)
    rw [hmap] at h
    simpa [smallW, tileW, cubicalPaddedWilsonExpectation,
      cubicalInteriorBlockTileLoop, L0, inner, target, A, C, N] using h
  have hsmall_nonneg : 0 <= smallW :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (p + L + p) (p + L + p) (p + p) => K)
      (fun _ => hK) _).1
  have hprod : smallW ^ (k * k) <=
      ∏ q : Fin k × Fin k, tileW q := by
    have hp := Finset.prod_le_prod
      (s := (Finset.univ : Finset (Fin k × Fin k)))
      (f := fun _ => smallW) (g := tileW)
      (fun _ _ => hsmall_nonneg) (fun q _ => htile q)
    simpa using hp
  have hglue := gaugeWilsonExpectation_prod_boundary_le_biUnion
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette N N N => K) (fun _ => hK)
    (Finset.univ : Finset (Fin k × Fin k))
    (cubicalInteriorBlockTileSheet L p k)
    (cubicalInteriorBlockTileSheet_pairwise_disjoint L p k hL)
  dsimp [N] at hglue
  simp_rw [← cubicalInteriorBlockTileLoop_eq_boundary] at hglue
  rw [cubicalInteriorBlockTileSheet_biUnion L p k hL] at hglue
  rw [← cubicalInteriorBlockCentralLoop_eq_boundary] at hglue
  exact hprod.trans (by simpa [smallW, tileW, N] using hglue)


theorem cubicalInteriorBlockCentralDisorderFreeEnergy_le_tiles
    {K : Real} (hK : 0 < K) (L p k : Nat)
    (hL : 0 < L) (hp : 0 < p) (hk : 0 < k) :
    multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
        (cubicalInteriorBlockCentralSheet L p k) <=
      (k * k : Nat) *
        cubicalPaddedDisorderFreeEnergy K L L p p p p p p := by
  let N := cubicalInteriorBlockSide L p k
  let Wp := cubicalPaddedWilsonExpectation K L L p p p p p p
  let Wc := gaugeWilsonExpectation cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette N N N => K)
    (cubicalInteriorBlockCentralLoop L p k)
  have hpow : Wp ^ (k * k) <= Wc := by
    simpa [Wp, Wc, N] using
      cubicalPaddedWilsonExpectation_pow_sq_le_interiorBlockCentral
        hK L p k hL
  have hpW : 0 < Wp := cubicalPaddedWilsonExpectation_pos hK
    L L p p p p p p
  have hcW : 0 < Wc := by
    dsimp [Wc]
    rw [cubicalInteriorBlockCentralLoop_eq_boundary]
    apply (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence (fun _ : CubicalPlaquette N N N => K)
      (fun _ => hK) _).2
    exact ⟨cubicalInteriorBlockCentralSheet L p k,
      hasWilsonBoundary_gaugeSurfaceBoundary _ _⟩
  have hlog := Real.log_le_log (pow_pos hpW (k * k)) hpow
  rw [Real.log_pow] at hlog
  have hcentral :=
    neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface
      (A := N) (B := N) (C := N)
      (by dsimp [N, cubicalInteriorBlockSide]; positivity)
      (by dsimp [N, cubicalInteriorBlockSide]; positivity)
      (by dsimp [N, cubicalInteriorBlockSide]; positivity)
      (fun _ : CubicalPlaquette N N N => K) (fun _ => hK)
      (cubicalInteriorBlockCentralSheet L p k)
  have hpadded :=
    neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
      (a := L) (b := L) (lx := p) (rx := p) (ly := p) (ry := p)
      (lz := p) (rz := p) hK hL hL (by omega)
  change multibondDisorderFreeEnergy cubicalDualEnds
      (fun _ : CubicalPlaquette N N N => gaugeDualCoupling K)
      (cubicalInteriorBlockCentralSheet L p k) <= _
  rw [← hcentral]
  rw [show cubicalPaddedDisorderFreeEnergy K L L p p p p p p =
      -Real.log Wp by
    dsimp [Wp]
    simpa [cubicalPaddedDisorderFreeEnergy] using hpadded.symm]
  dsimp [Wp, Wc] at hlog
  rw [cubicalInteriorBlockCentralLoop_eq_boundary] at hlog
  linarith

def cubicalInteriorBlockFullSheet (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalXYSheet (cubicalInteriorBlockHeight L p k)

theorem cubicalInteriorBlockCentralSheet_subset_full
    (L p k : Nat) :
    cubicalInteriorBlockCentralSheet L p k ⊆
      cubicalInteriorBlockFullSheet L p k := by
  intro plaquette hpq
  cases plaquette with
  | xy x y z =>
      simp only [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hpq
      obtain ⟨_, ⟨ij, _, rfl⟩, hpq⟩ := hpq
      unfold cubicalInteriorBlockFullSheet cubicalXYSheet
      apply Finset.mem_image.mpr
      refine ⟨((finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) ij.1),
        (finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) ij.2)),
        Finset.mem_univ _, ?_⟩
      change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z
      rw [CubicalPlaquette.xy.injEq]
      exact ⟨(CubicalPlaquette.xy.inj hpq).1,
        (CubicalPlaquette.xy.inj hpq).2.1,
        (CubicalPlaquette.xy.inj hpq).2.2.trans (by
          apply Fin.ext
          rfl)⟩
  | xz x y z =>
      simp [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq
  | yz x y z =>
      simp [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq

def cubicalInteriorBlockFrame (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalInteriorBlockFullSheet L p k \
    cubicalInteriorBlockCentralSheet L p k

theorem cubicalInteriorBlockFull_symmDiff_central
    (L p k : Nat) :
    cubicalInteriorBlockFullSheet L p k ∆
        cubicalInteriorBlockCentralSheet L p k =
      cubicalInteriorBlockFrame L p k := by
  have hsub := cubicalInteriorBlockCentralSheet_subset_full L p k
  ext plaquette
  simp only [Finset.mem_symmDiff, cubicalInteriorBlockFrame,
    Finset.mem_sdiff]
  constructor
  · rintro (⟨hfull, hnot⟩ | ⟨hcentral, hnot⟩)
    · exact ⟨hfull, hnot⟩
    · exact (hnot (hsub hcentral)).elim
  · rintro ⟨hfull, hnot⟩
    exact Or.inl ⟨hfull, hnot⟩

theorem card_cubicalInteriorBlockFrame (L p k : Nat) :
    (cubicalInteriorBlockFrame L p k).card =
      (cubicalInteriorBlockSide L p k) ^ 2 - (k * L) ^ 2 := by
  rw [cubicalInteriorBlockFrame,
    Finset.card_sdiff_of_subset
      (cubicalInteriorBlockCentralSheet_subset_full L p k)]
  congr 1
  · simp [cubicalInteriorBlockFullSheet, pow_two]
  · simp [cubicalInteriorBlockCentralSheet, pow_two]



theorem cubicalInteriorBlockFullDisorderFreeEnergy_le_central_add_frame
    {K : Real} (hK : 0 < K) (L p k : Nat) :
    multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
        (cubicalInteriorBlockFullSheet L p k) <=
      multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ : CubicalPlaquette
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
          (cubicalInteriorBlockCentralSheet L p k) +
        2 * (cubicalInteriorBlockFrame L p k).card * gaugeDualCoupling K := by
  let J := fun _ : CubicalPlaquette
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K
  have hdist := multibondDisorderFreeEnergy_sheet_sub_abs_le
    cubicalDualEnds J (cubicalInteriorBlockFullSheet L p k)
      (cubicalInteriorBlockCentralSheet L p k)
  rw [cubicalInteriorBlockFull_symmDiff_central] at hdist
  have hJ : 0 < gaugeDualCoupling K := gaugeDualCoupling_pos hK
  have hone := (le_abs_self
    (multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockFullSheet L p k) -
      multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockCentralSheet L p k))).trans hdist
  have hsum : (∑ q ∈ cubicalInteriorBlockFrame L p k, |J q|) =
      ((cubicalInteriorBlockFrame L p k).card : Real) *
        gaugeDualCoupling K := by
    simp [J, abs_of_pos hJ]
  rw [hsum] at hone
  dsimp [J] at hone ⊢
  linarith

def cubicalInteriorBlockBottomSheet (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalXYSheet (0 : Fin (cubicalInteriorBlockSide L p k + 1))

def cubicalInteriorBlockSlabComplement (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalLowerComplementSurface (cubicalInteriorBlockHeight L p k)


def cubicalInteriorBlockSideWallFaces (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  let N := cubicalInteriorBlockSide L p k
  let castZ : Fin p -> Fin N := Fin.castLE (by
    dsimp [N, cubicalInteriorBlockSide]
    omega)
  ((Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
      CubicalPlaquette.xz iz.1 (0 : Fin (N + 1)) (castZ iz.2)) ∪
  ((Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
      CubicalPlaquette.xz iz.1 (Fin.last N) (castZ iz.2)) ∪
  ((Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
      CubicalPlaquette.yz (0 : Fin (N + 1)) jz.1 (castZ jz.2)) ∪
  ((Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
      CubicalPlaquette.yz (Fin.last N) jz.1 (castZ jz.2))

theorem cubicalInteriorBlockBottomSheet_subset_slabComplement
    (L p k : Nat) (hp : 0 < p) :
    cubicalInteriorBlockBottomSheet L p k ⊆
      cubicalInteriorBlockSlabComplement L p k := by
  intro plaquette hplaquette
  rcases Finset.mem_image.mp hplaquette with ⟨ij, _, rfl⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_multibondCut]
    let z0 : Fin (cubicalInteriorBlockSide L p k) :=
      ⟨0, by simp [cubicalInteriorBlockSide]; omega⟩
    have hf : finForward
        (0 : Fin (cubicalInteriorBlockSide L p k + 1)) = some z0 := by
      rw [finForward_eq_some_iff]
      apply Fin.ext
      rfl
    have hb : finBackward
        (0 : Fin (cubicalInteriorBlockSide L p k + 1)) = none :=
      (finBackward_eq_none_iff _).2 rfl
    simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
      cubicalInteriorBlockHeight, z0, hp]
  · intro htop
    simp only [cubicalXYSheet, Finset.mem_image, Finset.mem_univ,
      true_and] at htop
    obtain ⟨xy, hxy⟩ := htop
    have hz := (CubicalPlaquette.xy.inj hxy).2.2
    have hzval := congrArg Fin.val hz
    simp [cubicalInteriorBlockHeight] at hzval
    omega

def cubicalInteriorBlockSlabSideWall (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalInteriorBlockSlabComplement L p k \
    cubicalInteriorBlockBottomSheet L p k

theorem cubicalInteriorBlockSlabComplement_symmDiff_bottom
    (L p k : Nat) (hp : 0 < p) :
    cubicalInteriorBlockSlabComplement L p k ∆
        cubicalInteriorBlockBottomSheet L p k =
      cubicalInteriorBlockSlabSideWall L p k := by
  have hsub := cubicalInteriorBlockBottomSheet_subset_slabComplement L p k hp
  ext plaquette
  simp only [Finset.mem_symmDiff, cubicalInteriorBlockSlabSideWall,
    Finset.mem_sdiff]
  constructor
  · rintro (⟨hcomp, hnot⟩ | ⟨hbottom, hnot⟩)
    · exact ⟨hcomp, hnot⟩
    · exact (hnot (hsub hbottom)).elim
  · rintro ⟨hcomp, hnot⟩
    exact Or.inl ⟨hcomp, hnot⟩

theorem cubicalInteriorBlockSlabSideWall_subset_faces
    (L p k : Nat) (hp : 0 < p) :
    cubicalInteriorBlockSlabSideWall L p k ⊆
      cubicalInteriorBlockSideWallFaces L p k := by
  let N := cubicalInteriorBlockSide L p k
  have hpN : p <= N := by dsimp [N, cubicalInteriorBlockSide]; omega
  intro plaquette hplaquette
  have hcomp := (Finset.mem_sdiff.mp hplaquette).1
  have hcut := (Finset.mem_sdiff.mp hcomp).1
  cases plaquette with
  | xy i j f =>
      have hnotBottom := (Finset.mem_sdiff.mp hplaquette).2
      have hnotTop := (Finset.mem_sdiff.mp hcomp).2
      rw [mem_multibondCut] at hcut
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          exfalso
          apply hnotBottom
          unfold cubicalInteriorBlockBottomSheet cubicalXYSheet
          exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
      | some z =>
          cases hf : finForward f with
          | none =>
              have hflast : f = Fin.last N :=
                (finForward_eq_none_iff' f).mp hf
              have hfz : f = z.succ := (finBackward_eq_some_iff f z).mp hb
              have hz : z.val < p := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              have hzlast := congrArg Fin.val (hfz.symm.trans hflast)
              simp at hzlast
              dsimp [N, cubicalInteriorBlockSide] at hzlast
              omega
          | some z' =>
              have hne : (z.val < p) ≠ (z'.val < p) := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              have hfz : f = z.succ := (finBackward_eq_some_iff f z).mp hb
              have hfz' : f = z'.castSucc :=
                (finForward_eq_some_iff f z').mp hf
              have hsucc : z'.val = z.val + 1 := by
                have h := congrArg Fin.val (hfz.symm.trans hfz')
                simp at h
                omega
              have hfp : f.val = p := by
                by_cases hz : z.val < p <;>
                  by_cases hz' : z'.val < p <;>
                    simp [hz, hz'] at hne <;> rw [hfz] <;> simp <;> omega
              exfalso
              apply hnotTop
              unfold cubicalXYSheet
              exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, by
                rw [CubicalPlaquette.xy.injEq]
                exact ⟨rfl, rfl, Fin.ext hfp.symm⟩⟩
  | xz i f z =>
      rw [mem_multibondCut] at hcut
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let y0 : Fin N := ⟨0, by dsimp [N, cubicalInteriorBlockSide]; omega⟩
          have hf : finForward (0 : Fin (N + 1)) = some y0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < p := by
            simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
              cubicalInteriorBlockHeight, y0] using hcut
          let zp : Fin p := ⟨z.val, hz⟩
          simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
            Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl (Or.inl (Or.inl ⟨(i, zp), by
            congr 1⟩))
      | some y =>
          cases hf : finForward f with
          | none =>
              have hlast : f = Fin.last N := (finForward_eq_none_iff' f).mp hf
              have hz : z.val < p := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              let zp : Fin p := ⟨z.val, hz⟩
              simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
                Finset.mem_image, Finset.mem_univ, true_and]
              exact Or.inl (Or.inl (Or.inr ⟨(i, zp), by
                rw [hlast]
                congr 1⟩))
          | some y' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                cubicalInteriorBlockHeight] at hcut
  | yz f j z =>
      rw [mem_multibondCut] at hcut
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let x0 : Fin N := ⟨0, by dsimp [N, cubicalInteriorBlockSide]; omega⟩
          have hf : finForward (0 : Fin (N + 1)) = some x0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < p := by
            simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
              cubicalInteriorBlockHeight, x0] using hcut
          let zp : Fin p := ⟨z.val, hz⟩
          simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
            Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl (Or.inr ⟨(j, zp), by
            congr 1⟩)
      | some x =>
          cases hf : finForward f with
          | none =>
              have hlast : f = Fin.last N := (finForward_eq_none_iff' f).mp hf
              have hz : z.val < p := by
                simpa [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  cubicalInteriorBlockHeight] using hcut
              let zp : Fin p := ⟨z.val, hz⟩
              simp only [cubicalInteriorBlockSideWallFaces, Finset.mem_union,
                Finset.mem_image, Finset.mem_univ, true_and]
              exact Or.inr ⟨(j, zp), by
                rw [hlast]
                congr 1⟩
          | some x' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                cubicalInteriorBlockHeight] at hcut

theorem card_cubicalInteriorBlockSideWallFaces_le
    (L p k : Nat) :
    (cubicalInteriorBlockSideWallFaces L p k).card <=
      4 * cubicalInteriorBlockSide L p k * p := by
  let N := cubicalInteriorBlockSide L p k
  let castZ : Fin p -> Fin N := Fin.castLE (by
    dsimp [N, cubicalInteriorBlockSide]
    omega)
  let west := (Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
    CubicalPlaquette.xz iz.1 (0 : Fin (N + 1)) (castZ iz.2)
  let east := (Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
    CubicalPlaquette.xz iz.1 (Fin.last N) (castZ iz.2)
  let south := (Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
    CubicalPlaquette.yz (0 : Fin (N + 1)) jz.1 (castZ jz.2)
  let north := (Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
    CubicalPlaquette.yz (Fin.last N) jz.1 (castZ jz.2)
  have hcard (S : Finset (CubicalPlaquette N N N))
      (hS : S = west ∨ S = east ∨ S = south ∨ S = north) :
      S.card <= N * p := by
    rcases hS with rfl | rfl | rfl | rfl <;>
      exact (Finset.card_image_le.trans_eq (by simp)).trans le_rfl
  change (west ∪ east ∪ south ∪ north).card <= 4 * N * p
  calc
    (west ∪ east ∪ south ∪ north).card <=
        west.card + east.card + south.card + north.card := by
      calc
        _ <= (west ∪ east ∪ south).card + north.card :=
          Finset.card_union_le _ _
        _ <= ((west ∪ east).card + south.card) + north.card := by
          gcongr
          exact Finset.card_union_le _ _
        _ <= ((west.card + east.card) + south.card) + north.card := by
          gcongr
          exact Finset.card_union_le _ _
    _ <= N * p + N * p + N * p + N * p := by
      gcongr
      · exact hcard west (Or.inl rfl)
      · exact hcard east (Or.inr (Or.inl rfl))
      · exact hcard south (Or.inr (Or.inr (Or.inl rfl)))
      · exact hcard north (Or.inr (Or.inr (Or.inr rfl)))
    _ = 4 * N * p := by ring

theorem card_cubicalInteriorBlockSlabSideWall_le
    (L p k : Nat) (hp : 0 < p) :
    (cubicalInteriorBlockSlabSideWall L p k).card <=
      4 * cubicalInteriorBlockSide L p k * p := by
  exact Finset.card_le_card
    (cubicalInteriorBlockSlabSideWall_subset_faces L p k hp) |>.trans
      (card_cubicalInteriorBlockSideWallFaces_le L p k)



theorem cubicalInteriorBlockBottomDisorderFreeEnergy_le_full_add_sideWall
    {K : Real} (hK : 0 < K) (L p k : Nat) (hp : 0 < p) :
    multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
        (cubicalInteriorBlockBottomSheet L p k) <=
      multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ : CubicalPlaquette
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k)
            (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
          (cubicalInteriorBlockFullSheet L p k) +
        2 * (cubicalInteriorBlockSlabSideWall L p k).card *
          gaugeDualCoupling K := by
  let J := fun _ : CubicalPlaquette
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k)
    (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K
  have hslab : multibondDisorderFreeEnergy cubicalDualEnds J
      (cubicalInteriorBlockFullSheet L p k) =
      multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockSlabComplement L p k) := by
    exact multibondDisorderFreeEnergy_sheet_eq_lowerComplementSurface
      (cubicalInteriorBlockHeight L p k) (by
        simp [cubicalInteriorBlockHeight, hp]) J
  have hdist := multibondDisorderFreeEnergy_sheet_sub_abs_le
    cubicalDualEnds J (cubicalInteriorBlockBottomSheet L p k)
      (cubicalInteriorBlockSlabComplement L p k)
  have hsym : cubicalInteriorBlockBottomSheet L p k ∆
      cubicalInteriorBlockSlabComplement L p k =
      cubicalInteriorBlockSlabSideWall L p k := by
    rw [symmDiff_comm]
    exact cubicalInteriorBlockSlabComplement_symmDiff_bottom L p k hp
  rw [hsym] at hdist
  have hJ : 0 < gaugeDualCoupling K := gaugeDualCoupling_pos hK
  have hsum : (∑ q ∈ cubicalInteriorBlockSlabSideWall L p k, |J q|) =
      ((cubicalInteriorBlockSlabSideWall L p k).card : Real) *
        gaugeDualCoupling K := by
    simp [J, abs_of_pos hJ]
  rw [hsum] at hdist
  have hone := (le_abs_self
    (multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockBottomSheet L p k) -
      multibondDisorderFreeEnergy cubicalDualEnds J
        (cubicalInteriorBlockSlabComplement L p k))).trans hdist
  rw [← hslab] at hone
  dsimp [J] at hone ⊢
  linarith



theorem cubicalRectangularWilsonFreeEnergy_interiorBlock_le
    {K : Real} (hK : 0 < K) (L p k : Nat)
    (hL : 0 < L) (hp : 0 < p) (hk : 0 < k) :
    cubicalRectangularWilsonFreeEnergy K
        (cubicalInteriorBlockSide L p k)
        (cubicalInteriorBlockSide L p k) <=
      (k * k : Nat) *
          cubicalPaddedDisorderFreeEnergy K L L p p p p p p +
        16 * cubicalInteriorBlockSide L p k * p * gaugeDualCoupling K := by
  let N := cubicalInteriorBlockSide L p k
  let J := gaugeDualCoupling K
  let P := cubicalPaddedDisorderFreeEnergy K L L p p p p p p
  have hcentral := cubicalInteriorBlockCentralDisorderFreeEnergy_le_tiles
    hK L p k hL hp hk
  have hframe := cubicalInteriorBlockFullDisorderFreeEnergy_le_central_add_frame
    hK L p k
  have hside := cubicalInteriorBlockBottomDisorderFreeEnergy_le_full_add_sideWall
    hK L p k hp
  have hframeCard : (cubicalInteriorBlockFrame L p k).card <= 4 * N * p := by
    rw [card_cubicalInteriorBlockFrame]
    have hsq : N ^ 2 = (k * L) ^ 2 + 4 * p * (k * L + p) := by
      dsimp [N, cubicalInteriorBlockSide]
      ring
    rw [hsq, Nat.add_sub_cancel_left]
    dsimp [N, cubicalInteriorBlockSide]
    nlinarith
  have hsideCard : (cubicalInteriorBlockSlabSideWall L p k).card <=
      4 * N * p := card_cubicalInteriorBlockSlabSideWall_le L p k hp
  have hJ : 0 <= J := (gaugeDualCoupling_pos hK).le
  have hframeReal :
      ((cubicalInteriorBlockFrame L p k).card : Real) <= 4 * N * p := by
    exact_mod_cast hframeCard
  have hsideReal :
      ((cubicalInteriorBlockSlabSideWall L p k).card : Real) <= 4 * N * p := by
    exact_mod_cast hsideCard
  have hbottom :
      multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ : CubicalPlaquette N N N => J)
          (cubicalInteriorBlockBottomSheet L p k) <=
        (k * k : Nat) * P + 16 * N * p * J := by
    dsimp [N, J, P] at hcentral hframe hside ⊢
    calc
      _ <= multibondDisorderFreeEnergy cubicalDualEnds
            (fun _ : CubicalPlaquette
              (cubicalInteriorBlockSide L p k)
              (cubicalInteriorBlockSide L p k)
              (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
            (cubicalInteriorBlockFullSheet L p k) +
          2 * (cubicalInteriorBlockSlabSideWall L p k).card *
            gaugeDualCoupling K := hside
      _ <= (multibondDisorderFreeEnergy cubicalDualEnds
              (fun _ : CubicalPlaquette
                (cubicalInteriorBlockSide L p k)
                (cubicalInteriorBlockSide L p k)
                (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
              (cubicalInteriorBlockCentralSheet L p k) +
            2 * (cubicalInteriorBlockFrame L p k).card *
              gaugeDualCoupling K) +
          2 * (cubicalInteriorBlockSlabSideWall L p k).card *
            gaugeDualCoupling K := by gcongr
      _ <= (k * k : Nat) *
            cubicalPaddedDisorderFreeEnergy K L L p p p p p p +
          2 * (cubicalInteriorBlockFrame L p k).card *
              gaugeDualCoupling K +
          2 * (cubicalInteriorBlockSlabSideWall L p k).card *
              gaugeDualCoupling K := by linarith
      _ <= (k * k : Nat) *
            cubicalPaddedDisorderFreeEnergy K L L p p p p p p +
          16 * cubicalInteriorBlockSide L p k * p * gaugeDualCoupling K := by
            have hf := mul_le_mul_of_nonneg_right hframeReal hJ
            have hs := mul_le_mul_of_nonneg_right hsideReal hJ
            norm_num at hf hs ⊢
            nlinarith
  have hN : 0 < N := by dsimp [N, cubicalInteriorBlockSide]; omega
  rw [cubicalRectangularWilsonFreeEnergy_eq_finiteIsingDisorder hK hN hN]
  unfold finiteRectangularIsingDisorderFreeEnergy
  rw [Nat.max_self]
  simpa [N, J, P, cubicalInteriorBlockBottomSheet] using hbottom



theorem rectangularIsingSurfaceTension_le_paddedDisorderDensity
    {K : Real} (hK : 0 < K) (L p : Nat) (hL : 0 < L) (hp : 0 < p) :
    rectangularIsingSurfaceTension (gaugeDualCoupling K) <=
      cubicalPaddedDisorderFreeEnergy K L L p p p p p p / (L : Real) ^ 2 := by
  let P := cubicalPaddedDisorderFreeEnergy K L L p p p p p p
  let J := gaugeDualCoupling K
  let upper : Nat -> Real := fun k =>
    let t : Nat := k + 1
    let N : Nat := cubicalInteriorBlockSide L p t
    (((t : Real) ^ 2 * P + 16 * (N : Real) * p * J) / (N : Real) ^ 2)
  have hrate : ∀ k : Nat,
      rectangularIsingSurfaceTension (gaugeDualCoupling K) <= upper k := by
    intro k
    let t : Nat := k + 1
    let N : Nat := cubicalInteriorBlockSide L p t
    have hN : 0 < N := by dsimp [N, cubicalInteriorBlockSide]; omega
    have hraw := cubicalRectangularWilsonFreeEnergy_interiorBlock_le
      hK L p t hL hp (by dsimp [t]; omega)
    have hrate0 := rectangularSurfaceRate_le_density
      (fun m n => cubicalRectangularWilsonFreeEnergy_nonneg hK m n) hN hN
    rw [cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
      hK] at hrate0
    unfold rectangularSurfaceDensity at hrate0
    have hden : (0 : Real) < (N : Real) * (N : Real) := by positivity
    have hrawDiv := div_le_div_of_nonneg_right hraw hden.le
    dsimp [upper, t, N, P, J]
    rw [show ((N : Real) * (N : Real)) = (N : Real) ^ 2 by ring] at hrate0 hrawDiv
    simpa [t, N, pow_two] using hrate0.trans hrawDiv
  let u : Nat -> Real := fun k => (1 : Real) / (k + 1 : Real)
  let transformed : Nat -> Real := fun k =>
    (P + 16 * p * J * (L * u k + 2 * p * (u k) ^ 2)) /
      (L + 2 * p * u k) ^ 2
  have hu : Tendsto u atTop (nhds 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hnum : Tendsto
      (fun k => P + 16 * p * J * (L * u k + 2 * p * (u k) ^ 2))
      atTop (nhds P) := by
    have hinner : Tendsto
        (fun k => (L : Real) * u k + 2 * p * (u k) ^ 2)
        atTop (nhds 0) := by
      convert (tendsto_const_nhds.mul hu).add
        (tendsto_const_nhds.mul (hu.pow 2)) using 1 <;> norm_num
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hinner) using 1 <;>
      norm_num
  have hden : Tendsto (fun k => (L + 2 * p * u k) ^ 2)
      atTop (nhds ((L : Real) ^ 2)) := by
    have hbase : Tendsto (fun k => (L : Real) + 2 * p * u k)
        atTop (nhds ((L : Real) + 2 * p * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hu)
    simpa using hbase.pow 2
  have hLsq : ((L : Real) ^ 2) ≠ 0 := by positivity
  have htransformed : Tendsto transformed atTop
      (nhds (P / (L : Real) ^ 2)) := by
    exact hnum.div hden hLsq
  have heq : ∀ k, upper k = transformed k := by
    intro k
    dsimp [upper, transformed, u, P, J, cubicalInteriorBlockSide]
    push_cast
    field_simp
    ring
  have hupper : Tendsto upper atTop (nhds (P / (L : Real) ^ 2)) := by
    exact htransformed.congr' (Eventually.of_forall fun k => (heq k).symm)
  exact ge_of_tendsto hupper (Eventually.of_forall hrate)

end

end StatMech.FrontierA
