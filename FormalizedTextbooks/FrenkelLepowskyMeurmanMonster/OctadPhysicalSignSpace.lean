/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual physical octad signs as linear six-bit spaces. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPhysicalSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadSignSpace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadAffineSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Embed the canonical six-bit sign space in the actual physical octad. -/
def octadPhysicalSignMap (o : Fin 759) :
    OctadSignSpace →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  (octadPhysicalEmbedding o).comp octadSignRepresentative

/-- Actual preferred-Q negative patterns are the sign-space label vectors. -/
theorem octadPhysicalSignMap_label (o : Fin 759) (e : Fin 64) :
    octadPhysicalSignMap o (octadSignLabelEquiv e) =
      integerParity (griessOctadNegativeInteger o e) := by
  change octadPhysicalEmbedding o (octadSignRepresentative (octadSignLabelEquiv e)) = _
  rw [octadSignRepresentative_label, griessOctadNegative_embedding]

/-- Every physical octad sign pattern is supported on its own octad. -/
theorem octadPhysicalSignMap_supported (o : Fin 759) (x : OctadSignSpace) (i : Fin 24)
    (hi : i ∉ golayOctadSupport o) : octadPhysicalSignMap o x i = 0 := by
  apply octadPhysicalEmbedding_supported
  simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
    Finset.mem_univ, true_and] using hi

/-- Every physical octad sign pattern is even. -/
theorem octadPhysicalSignMap_even (o : Fin 759) (x : OctadSignSpace) :
    (∑ i, octadPhysicalSignMap o x i) = 0 := by
  change (∑ i, octadPhysicalEmbedding o (octadSignRepresentative x) i) = 0
  rw [octadPhysicalEmbedding_sum, octadSignRepresentative_even]

/-- The physical pairing is the canonical nondegenerate sign pairing. -/
theorem octadPhysicalSignMap_pairing (o : Fin 759) (x y : OctadSignSpace) :
    (∑ i, octadPhysicalSignMap o x i * octadPhysicalSignMap o y i) =
      octadSignForm x y := by
  change (∑ i, octadPhysicalEmbedding o (octadSignRepresentative x) i *
    octadPhysicalEmbedding o (octadSignRepresentative y) i) = _
  rw [octadPhysicalEmbedding_pairing]
  rfl

/-- Three canonical sign spaces carry the three-octad cubic. -/
abbrev OctadTripleSignSpace := Fin 3 → OctadSignSpace

/-- The direct sum of the three actual binary intersection forms. -/
def octadTripleForm :
    OctadTripleSignSpace →ₗ[ZMod 2] OctadTripleSignSpace →ₗ[ZMod 2] ZMod 2 where
  toFun x :=
    { toFun y := ∑ s, octadSignForm (x s) (y s)
      map_add' y z := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' a y := by
        simp only [Pi.smul_apply, map_smul, ← Finset.smul_sum, RingHom.id_apply] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change (∑ s, octadSignForm (x s+y s) (z s)) = _
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib,
      LinearMap.coe_mk, AddHom.coe_mk]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change (∑ s, octadSignForm (a • x s) (y s)) = _
    simp only [map_smul, LinearMap.smul_apply,
      ← Finset.smul_sum, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The actual triple form is symmetric. -/
theorem octadTripleForm_symmetric (x y : OctadTripleSignSpace) :
    octadTripleForm x y = octadTripleForm y x := by
  change (∑ s, octadSignForm (x s) (y s)) = ∑ s, octadSignForm (y s) (x s)
  simp_rw [octadSignForm_symmetric]

/-- Evaluate one coordinate in a sum of linear maps. -/
private theorem octad_sum_single (f : Fin 3 → OctadSignSpace →ₗ[ZMod 2] ZMod 2)
    (s : Fin 3) (v : OctadSignSpace) :
    (∑ k, f k ((Pi.single s v : OctadTripleSignSpace) k)) = f s v := by
  rw [Finset.sum_eq_single s]
  · simp only [Pi.single_eq_same]
  · intro k _ hks
    simp [hks]
  · simp

/-- The actual triple form has trivial radical. -/
theorem octadTripleForm_nondegenerate (x : OctadTripleSignSpace)
    (hx : ∀ y, octadTripleForm x y = 0) : x = 0 := by
  apply funext
  intro s
  apply octadSignForm_nondegenerate
  intro v
  have h := hx (Pi.single s v)
  change (∑ k, octadSignForm (x k) ((Pi.single s v : OctadTripleSignSpace) k)) = 0 at h
  exact (octad_sum_single (fun k => octadSignForm (x k)) s v).symm.trans h

/-- The published octad word is one on each local coordinate. -/
theorem golayOctadWord_local (o : Fin 759) (k : Fin 8) :
    golayOctadWord o (golayOctadCoordinate o k) = 1 := by
  simp [golayOctadWord, golayLabelEncoder_boolean, golayOctadCoordinate_mem,
    golayBooleanCast]

/-- Constant local signs embed as a scalar multiple of the octad codeword. -/
theorem octadPhysicalEmbedding_constant (o : Fin 759) (a : ZMod 2) :
    octadPhysicalEmbedding o (fun _ => a) = a • golayOctadWord o := by
  ext i
  by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
  · obtain ⟨k, rfl⟩ := golayOctadCoordinate_surjective o i hi
    simp only [octadPhysicalEmbedding_local, Pi.smul_apply, golayOctadWord_local,
      smul_eq_mul, mul_one]
  · rw [octadPhysicalEmbedding_supported o _ i hi]
    simp [golayOctadWord, golayLabelEncoder_boolean, hi, golayBooleanCast]

/-- Pulling back a supported physical pattern and embedding it recovers the pattern. -/
theorem octadPhysicalEmbedding_pullback (o : Fin 759) (x : Fin 24 → ZMod 2)
    (hs : ∀ i, i ∉ golayOctadSupport o → x i = 0) :
    octadPhysicalEmbedding o (fun k => x (golayOctadCoordinate o k)) = x := by
  ext i
  by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
  · obtain ⟨k, rfl⟩ := golayOctadCoordinate_surjective o i hi
    exact octadPhysicalEmbedding_local o _ k
  · rw [octadPhysicalEmbedding_supported o _ i hi]
    symm
    apply hs
    simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi

/-- Pull a physical pattern back and choose its six-bit complement representative. -/
def octadPhysicalNormalize (o : Fin 759) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] OctadSignSpace where
  toFun x := octadSignNormalize (fun k => x (golayOctadCoordinate o k))
  map_add' x y := by
    change octadSignNormalize (_+_) = _
    rw [map_add]
  map_smul' a x := by
    change octadSignNormalize (a • _) = _
    simp only [map_smul, RingHom.id_apply]

/-- Every supported even physical pattern is recovered modulo its full octad complement. -/
theorem octadPhysicalSignMap_normalize (o : Fin 759) (x : Fin 24 → ZMod 2)
    (hs : ∀ i, i ∉ golayOctadSupport o → x i = 0) (he : ∑ i, x i = 0) :
    octadPhysicalSignMap o (octadPhysicalNormalize o x) =
      x + x (golayOctadCoordinate o 7) • golayOctadWord o := by
  have hev : (∑ k : Fin 8, x (golayOctadCoordinate o k)) = 0 := by
    rw [← octadPhysicalEmbedding_sum, octadPhysicalEmbedding_pullback o x hs, he]
  change octadPhysicalEmbedding o
    (octadSignRepresentative (octadSignNormalize (fun k => x (golayOctadCoordinate o k)))) = _
  rw [octadSignRepresentative_normalize _ hev]
  change octadPhysicalEmbedding o
    ((fun k => x (golayOctadCoordinate o k)) + (fun _ => x (golayOctadCoordinate o 7))) = _
  rw [map_add, octadPhysicalEmbedding_pullback o x hs, octadPhysicalEmbedding_constant]

/-- Sum the three actual physical sign patterns. -/
def octadTriplePhysicalSum (o p u : Fin 759) :
    OctadTripleSignSpace →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun x := octadPhysicalSignMap o (x 0) + octadPhysicalSignMap p (x 1) +
    octadPhysicalSignMap u (x 2)
  map_add' x y := by simp only [Pi.add_apply, map_add]; abel
  map_smul' a x := by simp only [Pi.smul_apply, map_smul, smul_add, RingHom.id_apply]

/-- The actual homogeneous syndrome kernel underlying the octad cubic support. -/
def octadTripleSyndromeKernel (o p u : Fin 759) :
    Submodule (ZMod 2) OctadTripleSignSpace :=
  (golaySyndrome.comp (octadTriplePhysicalSum o p u)).ker

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
