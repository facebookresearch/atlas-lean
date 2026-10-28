/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadGenerators

/-! Adapted coordinates for the octad binary forest. The last eight coordinates are the pairings
with the image of the octad-three section, so the high byte records the induced action on its
dual and the low sixteen bits parametrize each fiber. All transition and inverse identities are
kernel checked. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Columns of the coordinate change from adapted to genuine hyperbolic coordinates. -/
def generatedAxisGlobalTwelveOctadTRows : List (ℕ × ℕ) :=
  [(0, 3), (1, 4), (2, 8), (3, 320), (4, 640), (5, 2048), (6, 12288), (7, 16384), (8, 32768),
    (9, 65536), (10, 131072), (11, 262144), (12, 524288), (13, 1048576), (14, 2097152),
    (15, 4194304), (16, 4096), (17, 8388608), (18, 1), (19, 16), (20, 32), (21, 64), (22, 128),
    (23, 1024)]

/-- Columns of the inverse coordinate change. -/
def generatedAxisGlobalTwelveOctadTinvRows : List (ℕ × ℕ) :=
  [(0, 262144), (1, 262145), (2, 2), (3, 4), (4, 524288), (5, 1048576), (6, 2097152),
    (7, 4194304), (8, 2097160), (9, 4194320), (10, 8388608), (11, 32), (12, 65536),
    (13, 65600), (14, 128), (15, 256), (16, 512), (17, 1024), (18, 2048), (19, 4096),
    (20, 8192), (21, 16384), (22, 32768), (23, 131072)]

/-- The sixteen generator actions in adapted coordinates. -/
def generatedAxisGlobalTwelveOctadCoordRows : Fin 16 → List (ℕ × ℕ) :=
  ![[(0, 32801), (1, 32802), (2, 32804), (3, 16392), (4, 8208), (5, 32), (6, 96), (7, 128),
      (8, 256), (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384),
      (15, 32768), (16, 65568), (17, 459200), (18, 262144), (19, 525312), (20, 1049088),
      (21, 2097152), (22, 4194304), (23, 8454592)],
    [(0, 32801), (1, 32802), (2, 32804), (3, 16392), (4, 8208), (5, 32), (6, 96), (7, 128),
      (8, 256), (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384),
      (15, 32768), (16, 65536), (17, 459137), (18, 294944), (19, 545792), (20, 1059328),
      (21, 2118656), (22, 4205056), (23, 8454528)],
    [(0, 1), (1, 2), (2, 32804), (3, 31752), (4, 21008), (5, 32), (6, 64), (7, 160), (8, 256),
      (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384), (15, 32768),
      (16, 65536), (17, 131394), (18, 294944), (19, 539648), (20, 1077760), (21, 2126336),
      (22, 4214272), (23, 8388928)],
    [(0, 1), (1, 32802), (2, 4), (3, 11272), (4, 31248), (5, 32), (6, 64), (7, 128), (8, 288),
      (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384), (15, 32768),
      (16, 65536), (17, 131268), (18, 294944), (19, 551936), (20, 1071616), (21, 2110976),
      (22, 4221952), (23, 8388800)],
    [(0, 20481), (1, 15394), (2, 27684), (3, 20488), (4, 31120), (5, 32), (6, 64), (7, 128),
      (8, 256), (9, 544), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384),
      (15, 32768), (16, 65536), (17, 655808), (18, 263200), (19, 524288), (20, 1049024),
      (21, 2113920), (22, 4284608), (23, 8388608)],
    [(0, 10241), (1, 29218), (2, 23076), (3, 31112), (4, 10256), (5, 32), (6, 64), (7, 128),
      (8, 256), (9, 512), (10, 1056), (11, 2048), (12, 4096), (13, 8192), (14, 16384),
      (15, 32768), (16, 65536), (17, 1180096), (18, 262688), (19, 524736), (20, 1048576),
      (21, 2187584), (22, 4202880), (23, 8388608)],
    [(0, 21537), (1, 29218), (2, 13860), (3, 1416), (4, 1808), (5, 32), (6, 64), (7, 128),
      (8, 256), (9, 512), (10, 1024), (11, 2080), (12, 4096), (13, 8192), (14, 16384),
      (15, 32768), (16, 65536), (17, 2294208), (18, 262144), (19, 541056), (20, 1139008),
      (21, 2097152), (22, 4260288), (23, 8388608)],
    [(0, 10785), (1, 20002), (2, 27684), (3, 1672), (4, 912), (5, 32), (6, 64), (7, 128),
      (8, 256), (9, 512), (10, 1024), (11, 2048), (12, 4128), (13, 8192), (14, 16384),
      (15, 32768), (16, 65536), (17, 4391360), (18, 262144), (19, 614592), (20, 1057152),
      (21, 2163136), (22, 4194304), (23, 8388608)],
    [(0, 21537), (1, 3586), (2, 6660), (3, 1416), (4, 34640), (5, 32), (6, 64), (7, 128),
      (8, 256), (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8224), (14, 16384),
      (15, 32768), (16, 65536), (17, 2326536), (18, 278560), (19, 528768), (20, 1120448),
      (21, 2098560), (22, 4261696), (23, 8405024)],
    [(0, 10785), (1, 7170), (2, 5636), (3, 34504), (4, 912), (5, 32), (6, 64), (7, 128),
      (8, 256), (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16416),
      (15, 32768), (16, 65536), (17, 4423696), (18, 270368), (19, 596288), (20, 1051008),
      (21, 2164416), (22, 4195200), (23, 8396832)],
    [(0, 65), (1, 322), (2, 196), (3, 16392), (4, 8208), (5, 32), (6, 64), (7, 128), (8, 256),
      (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384), (15, 32800),
      (16, 65536), (17, 8519680), (18, 328128), (19, 524288), (20, 1048576), (21, 2097152),
      (22, 4194304), (23, 8388608)],
    [(0, 1), (1, 2), (2, 4), (3, 8), (4, 16), (5, 32), (6, 64), (7, 128), (8, 256), (9, 512),
      (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384), (15, 32768), (16, 65536),
      (17, 131072), (18, 262144), (19, 524288), (20, 1048576), (21, 2097152), (22, 4194304),
      (23, 8388608)],
    [(0, 20993), (1, 20994), (2, 8821), (3, 55131), (4, 10320), (5, 32), (6, 64), (7, 23232),
      (8, 21248), (9, 30784), (10, 11328), (11, 2048), (12, 39168), (13, 8192), (14, 45888),
      (15, 53760), (16, 121600), (17, 164160), (18, 6076210), (19, 12683671), (20, 1050688),
      (21, 7882243), (22, 8986775), (23, 8397425)],
    [(0, 54849), (1, 19235), (2, 63689), (3, 63685), (4, 1245), (5, 32), (6, 10752),
      (7, 54976), (8, 57344), (9, 512), (10, 11840), (11, 61248), (12, 15360), (13, 60672),
      (14, 36864), (15, 31744), (16, 112000), (17, 164032), (18, 3224867), (19, 4041411),
      (20, 13714443), (21, 13923209), (22, 8509715), (23, 4322175)],
    [(0, 53825), (1, 44408), (2, 56997), (3, 787), (4, 33841), (5, 32), (6, 1024), (7, 23040),
      (8, 12032), (9, 54272), (10, 64), (11, 32960), (12, 24768), (13, 31360), (14, 13440),
      (15, 22016), (16, 79104), (17, 135616), (18, 7459489), (19, 10560782), (20, 13375380),
      (21, 2118030), (22, 15281467), (23, 2703744)],
    [(0, 64), (1, 320), (2, 192), (3, 8), (4, 16), (5, 32768), (6, 65), (7, 133), (8, 259),
      (9, 512), (10, 1024), (11, 2048), (12, 4096), (13, 8192), (14, 16384), (15, 32800),
      (16, 327687), (17, 8519680), (18, 65984), (19, 524288), (20, 1048576), (21, 2097152),
      (22, 4194304), (23, 131072)]]

set_option maxHeartbeats 4000000 in
-- Check the 24 composed unit columns.
/-- The coordinate change composed with its inverse has the unit columns. -/
theorem generatedAxisGlobalTwelveOctadT_Tinv_certificate :
    generatedAxisGlobalTwelveOctadTinvRows.map
        (fun p => (p.1,
          generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows p.2)) =
      List.ofFn (fun j : Fin 24 => (j.val, 2 ^ j.val)) := by
  decide +kernel

/-- The coordinate change undoes its inverse on every genuine mask. -/
theorem generatedAxisGlobalTwelveOctadT_Tinv (b : ℕ) (hb : b < 2 ^ 24) :
    generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows
        (generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTinvRows b) = b := by
  rw [generatedAxisGlobalTwelveOctadRows_comp, generatedAxisGlobalTwelveOctadT_Tinv_certificate,
    generatedAxisGlobalTwelveOctadRows_unit b hb]

set_option maxHeartbeats 4000000 in
-- Check the bound of all 48 displayed columns.
/-- All displayed coordinate-change columns lie in the 24 genuine coordinates. -/
theorem generatedAxisGlobalTwelveOctadTRows_bounds :
    (∀ p ∈ generatedAxisGlobalTwelveOctadTRows, p.2 < 2 ^ 24) ∧
      (∀ p ∈ generatedAxisGlobalTwelveOctadTinvRows, p.2 < 2 ^ 24) := by
  decide +kernel

/-- The inverse coordinate change stays in the genuine 24-bit domain. -/
theorem generatedAxisGlobalTwelveOctadTinv_lt (b : ℕ) :
    generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTinvRows b < 2 ^ 24 :=
  generatedAxisGlobalMaskRowsAction_lt 24 _ generatedAxisGlobalTwelveOctadTRows_bounds.2 b

/-- The coordinate change stays in the genuine 24-bit domain. -/
theorem generatedAxisGlobalTwelveOctadT_lt (b : ℕ) :
    generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows b < 2 ^ 24 :=
  generatedAxisGlobalMaskRowsAction_lt 24 _ generatedAxisGlobalTwelveOctadTRows_bounds.1 b

set_option maxHeartbeats 40000000 in
-- Check all 384 adapted generator columns against the genuine generator masks.
/-- Each adapted generator is the inverse change, the genuine generator, and the change. -/
theorem generatedAxisGlobalTwelveOctadCoordRows_certificate : ∀ k : Fin 16,
    generatedAxisGlobalTwelveOctadCoordRows k =
      generatedAxisGlobalTwelveOctadTRows.map (fun p => (p.1,
        generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTinvRows
          (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadRows k) p.2))) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check that the low sixteen adapted columns of every generator stay low.
/-- Every generator preserves the span of the low sixteen adapted coordinates. -/
theorem generatedAxisGlobalTwelveOctadCoordRows_low : ∀ k : Fin 16,
    ∀ p ∈ generatedAxisGlobalTwelveOctadCoordRows k, p.1 < 16 → p.2 < 2 ^ 16 := by
  decide +kernel

/-- Adapted coordinates of a genuine binary Ω-orbit point. -/
noncomputable def generatedAxisGlobalTwelveOctadCoord (x : generatedAxisGlobalBinaryOrbit) : ℕ :=
  generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTinvRows
    (generatedAxisGlobalTwelveOctadMask x)

/-- Adapted coordinates stay in the 24-bit domain. -/
theorem generatedAxisGlobalTwelveOctadCoord_lt (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalTwelveOctadCoord x < 2 ^ 24 :=
  generatedAxisGlobalTwelveOctadTinv_lt _

/-- The genuine mask is recovered from the adapted coordinates. -/
theorem generatedAxisGlobalTwelveOctadMask_eq_coord (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalTwelveOctadMask x =
      generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows
        (generatedAxisGlobalTwelveOctadCoord x) :=
  (generatedAxisGlobalTwelveOctadT_Tinv _ (generatedAxisGlobalTwelveOctadMask_lt x)).symm

/-- Every actual generator acts on adapted coordinates by its adapted row list. -/
theorem generatedAxisGlobalTwelveOctadGenerator_coord (k : Fin 16)
    (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalTwelveOctadCoord
        (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadGenerator k).val x) =
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadCoordRows k)
        (generatedAxisGlobalTwelveOctadCoord x) := by
  have h1 : generatedAxisGlobalTwelveOctadCoord
      (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadGenerator k).val x) =
      generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTinvRows
        (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadRows k)
          (generatedAxisGlobalTwelveOctadMask x)) := by
    unfold generatedAxisGlobalTwelveOctadCoord
    rw [generatedAxisGlobalTwelveOctadGenerator_mask]
  rw [h1, generatedAxisGlobalTwelveOctadMask_eq_coord x,
    generatedAxisGlobalTwelveOctadCoordRows_certificate,
    generatedAxisGlobalTwelveOctadRows_comp (generatedAxisGlobalTwelveOctadRows k)
      generatedAxisGlobalTwelveOctadTRows,
    generatedAxisGlobalTwelveOctadRows_comp generatedAxisGlobalTwelveOctadTinvRows, List.map_map]
  rfl

/-- High adapted coordinates of a generator image depend only on the high coordinates. -/
theorem generatedAxisGlobalTwelveOctadGenerator_coord_high (k : Fin 16)
    (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalTwelveOctadCoord
        (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadGenerator k).val x) >>> 16 =
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadCoordRows k)
        ((generatedAxisGlobalTwelveOctadCoord x >>> 16) <<< 16) >>> 16 := by
  rw [generatedAxisGlobalTwelveOctadGenerator_coord]
  exact generatedAxisGlobalTwelveOctadRows_high _ (generatedAxisGlobalTwelveOctadCoordRows_low k) _

/-- The adapted row list of a generator word, composed from right to left. -/
def generatedAxisGlobalTwelveOctadWordRows (w : List (Fin 16)) : List (ℕ × ℕ) :=
  w.foldr (fun k r => r.map (fun p => (p.1,
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadCoordRows k) p.2)))
    (List.ofFn (fun j : Fin 24 => (j.val, 2 ^ j.val)))

/-- The actual local element of a generator word. -/
noncomputable def generatedAxisGlobalTwelveOctadWord (w : List (Fin 16)) : H :=
  (w.map (fun k => (generatedAxisGlobalTwelveOctadGenerator k).val)).prod

/-- Every generator word fixes the entire actual octad axis. -/
theorem generatedAxisGlobalTwelveOctadWord_mem (w : List (Fin 16)) :
    generatedAxisGlobalTwelveOctadWord w ∈ generatedOctadLocalAxisStabilizer 0 0 := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons k w ih =>
      simp only [generatedAxisGlobalTwelveOctadWord, List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _ (generatedAxisGlobalTwelveOctadGenerator k).property ih

private theorem octadBinaryActOne (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalBinaryAct 1 x = x := by
  apply Subtype.ext
  change co1BinaryAction (projH 1) x.val = x.val
  rw [map_one, map_one]
  rfl

/-- Every generator word acts on adapted coordinates by its composed row list. -/
theorem generatedAxisGlobalTwelveOctadWord_coord (w : List (Fin 16))
    (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalTwelveOctadCoord
        (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadWord w) x) =
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadWordRows w)
        (generatedAxisGlobalTwelveOctadCoord x) := by
  induction w with
  | nil =>
      simp only [generatedAxisGlobalTwelveOctadWord, List.map_nil, List.prod_nil,
        octadBinaryActOne, generatedAxisGlobalTwelveOctadWordRows, List.foldr_nil]
      exact (generatedAxisGlobalTwelveOctadRows_unit _
        (generatedAxisGlobalTwelveOctadCoord_lt x)).symm
  | cons k w ih =>
      have he : generatedAxisGlobalTwelveOctadWord (k :: w) =
          (generatedAxisGlobalTwelveOctadGenerator k).val * generatedAxisGlobalTwelveOctadWord w :=
        rfl
      rw [he, generatedAxisGlobalBinaryAct_mul, generatedAxisGlobalTwelveOctadGenerator_coord, ih,
        generatedAxisGlobalTwelveOctadRows_comp]
      rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
