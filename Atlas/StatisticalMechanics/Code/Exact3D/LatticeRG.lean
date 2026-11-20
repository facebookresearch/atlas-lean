/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Exact3D.RG
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice










namespace StatMech
namespace Exact3D

open StatMech.Lattice


abbrev BlockIndex (d : ℕ) : Type :=
  Site d



def blockIndexOf {d : ℕ} (scale : BlockScale) (x : Site d) : BlockIndex d :=
  fun i => x i / (scale.L : ℤ)


def blockRepresentative {d : ℕ} (scale : BlockScale) (b : BlockIndex d) : Site d :=
  fun i => (scale.L : ℤ) * b i

@[simp] theorem blockRepresentative_apply {d : ℕ} (scale : BlockScale)
    (b : BlockIndex d) (i : Fin d) :
    blockRepresentative scale b i = (scale.L : ℤ) * b i :=
  rfl

@[simp] theorem blockRepresentative_zero {d : ℕ} (scale : BlockScale) :
    blockRepresentative scale (0 : BlockIndex d) = (0 : Site d) := by
  ext i
  simp [blockRepresentative]

@[simp] theorem blockIndexOf_blockRepresentative {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) :
    blockIndexOf scale (blockRepresentative scale b) = b := by
  ext i
  simpa [blockIndexOf, blockRepresentative] using
    Int.mul_ediv_cancel_left (b i) (Int.ofNat_ne_zero.mpr scale.L_ne_zero)

@[simp] theorem blockIndexOf_zero {d : ℕ} (scale : BlockScale) :
    blockIndexOf scale (0 : Site d) = (0 : BlockIndex d) := by
  ext i
  simp [blockIndexOf]


def blockRemainder {d : ℕ} (scale : BlockScale) (x : Site d) : Site d :=
  fun i => x i % (scale.L : ℤ)

@[simp] theorem blockRemainder_apply {d : ℕ} (scale : BlockScale)
    (x : Site d) (i : Fin d) :
    blockRemainder scale x i = x i % (scale.L : ℤ) :=
  rfl

theorem blockRepresentative_blockIndexOf_add_blockRemainder {d : ℕ}
    (scale : BlockScale) (x : Site d) :
    blockRepresentative scale (blockIndexOf scale x) +
        blockRemainder scale x = x := by
  ext i
  simpa [blockRepresentative, blockIndexOf, blockRemainder] using
    Int.mul_ediv_add_emod (x i) (scale.L : ℤ)

theorem blockRemainder_nonneg {d : ℕ}
    (scale : BlockScale) (x : Site d) (i : Fin d) :
    0 ≤ blockRemainder scale x i := by
  simpa [blockRemainder] using
    Int.emod_nonneg (x i) (Int.ofNat_ne_zero.mpr scale.L_ne_zero)

theorem blockRemainder_lt_scale {d : ℕ}
    (scale : BlockScale) (x : Site d) (i : Fin d) :
    blockRemainder scale x i < (scale.L : ℤ) := by
  simpa [blockRemainder] using
    Int.emod_lt_of_pos (x i) (show 0 < (scale.L : ℤ) by
      exact_mod_cast lt_trans Nat.zero_lt_one scale.one_lt)

theorem blockRemainder_natAbs_lt_scale {d : ℕ}
    (scale : BlockScale) (x : Site d) (i : Fin d) :
    (blockRemainder scale x i).natAbs < scale.L := by
  have hcast :
      ((blockRemainder scale x i).natAbs : ℤ) < (scale.L : ℤ) := by
    rw [Int.natCast_natAbs,
      abs_of_nonneg (blockRemainder_nonneg scale x i)]
    exact blockRemainder_lt_scale scale x i
  exact_mod_cast hcast

@[simp] theorem blockRemainder_zero {d : ℕ} (scale : BlockScale) :
    blockRemainder scale (0 : Site d) = (0 : Site d) := by
  ext i
  simp [blockRemainder]

@[simp] theorem blockRemainder_blockRepresentative {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) :
    blockRemainder scale (blockRepresentative scale b) = (0 : Site d) := by
  ext i
  simp [blockRemainder, blockRepresentative, Int.mul_emod_right]



theorem blockRemainder_eq_zero_iff_exists_blockRepresentative {d : ℕ}
    (scale : BlockScale) (x : Site d) :
    blockRemainder scale x = 0 ↔
      ∃ b : BlockIndex d, blockRepresentative scale b = x := by
  constructor
  · intro hzero
    refine ⟨blockIndexOf scale x, ?_⟩
    have hdecomp :=
      blockRepresentative_blockIndexOf_add_blockRemainder scale x
    simpa [hzero] using hdecomp
  · rintro ⟨b, rfl⟩
    exact blockRemainder_blockRepresentative scale b

theorem blockIndexOf_blockRepresentative_add_of_remainder_bounds {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) (r : Site d)
    (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
    (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ)) :
    blockIndexOf scale (blockRepresentative scale b + r) = b := by
  ext i
  have hLne : (scale.L : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr scale.L_ne_zero
  have hdiv : r i / (scale.L : ℤ) = 0 :=
    Int.ediv_eq_zero_of_lt (hr_nonneg i) (hr_lt i)
  calc
    blockIndexOf scale (blockRepresentative scale b + r) i =
        ((scale.L : ℤ) * b i + r i) / (scale.L : ℤ) := rfl
    _ = (r i + (scale.L : ℤ) * b i) / (scale.L : ℤ) := by
      rw [add_comm]
    _ = r i / (scale.L : ℤ) + b i := by
      exact Int.add_mul_ediv_left (r i) (b i) hLne
    _ = b i := by
      simp [hdiv]

theorem blockRemainder_blockRepresentative_add_of_remainder_bounds {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) (r : Site d)
    (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
    (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ)) :
    blockRemainder scale (blockRepresentative scale b + r) = r := by
  ext i
  calc
    blockRemainder scale (blockRepresentative scale b + r) i =
        ((scale.L : ℤ) * b i + r i) % (scale.L : ℤ) := rfl
    _ = (r i + (scale.L : ℤ) * b i) % (scale.L : ℤ) := by
      rw [add_comm]
    _ = r i % (scale.L : ℤ) := by
      exact Int.add_mul_emod_self_left (r i) (scale.L : ℤ) (b i)
    _ = r i := Int.emod_eq_of_lt (hr_nonneg i) (hr_lt i)

theorem block_decomposition_unique {d : ℕ} (scale : BlockScale)
    {b c : BlockIndex d} {r s : Site d}
    (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
    (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ))
    (hs_nonneg : ∀ i : Fin d, 0 ≤ s i)
    (hs_lt : ∀ i : Fin d, s i < (scale.L : ℤ))
    (h :
      blockRepresentative scale b + r =
        blockRepresentative scale c + s) :
    b = c ∧ r = s := by
  have hb : b = c := by
    calc
      b = blockIndexOf scale (blockRepresentative scale b + r) :=
        (blockIndexOf_blockRepresentative_add_of_remainder_bounds
          scale b r hr_nonneg hr_lt).symm
      _ = blockIndexOf scale (blockRepresentative scale c + s) := by
        rw [h]
      _ = c :=
        blockIndexOf_blockRepresentative_add_of_remainder_bounds
          scale c s hs_nonneg hs_lt
  have hr : r = s := by
    calc
      r = blockRemainder scale (blockRepresentative scale b + r) :=
        (blockRemainder_blockRepresentative_add_of_remainder_bounds
          scale b r hr_nonneg hr_lt).symm
      _ = blockRemainder scale (blockRepresentative scale c + s) := by
        rw [h]
      _ = s :=
        blockRemainder_blockRepresentative_add_of_remainder_bounds
          scale c s hs_nonneg hs_lt
  exact ⟨hb, hr⟩




structure BlockSpinKernel (d : ℕ) where
  scale : BlockScale
  allowed : ConfigSpace (Site d) → ConfigSpace (BlockIndex d) → Prop


def deterministicKernel {d : ℕ} (scale : BlockScale)
    (coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d)) :
    BlockSpinKernel d where
  scale := scale
  allowed := fun σ τ => τ = coarse σ

theorem deterministicKernel_allowed {d : ℕ} (scale : BlockScale)
    (coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d))
    (σ : ConfigSpace (Site d)) :
    (deterministicKernel scale coarse).allowed σ (coarse σ) := by
  rfl

@[simp] theorem deterministicKernel_allowed_iff {d : ℕ} (scale : BlockScale)
    (coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d))
    (σ : ConfigSpace (Site d)) (τ : ConfigSpace (BlockIndex d)) :
    (deterministicKernel scale coarse).allowed σ τ ↔ τ = coarse σ :=
  Iff.rfl


structure RelevantCoordinates where
  thermal : ℝ
  magnetic : ℝ




structure EffectiveCoordinateChart where
  relevant : RelevantCoordinates
  irrelevant : ℕ → ℝ


structure PolymerSupport (d : ℕ) where
  carrier : Finset (Site d)

namespace PolymerSupport


def Contains {d : ℕ} (P : PolymerSupport d) (x : Site d) : Prop :=
  x ∈ P.carrier

instance {d : ℕ} : Membership (Site d) (PolymerSupport d) where
  mem P x := P.Contains x

@[simp] theorem mem_def {d : ℕ} (P : PolymerSupport d) (x : Site d) :
    x ∈ P ↔ x ∈ P.carrier :=
  Iff.rfl

@[ext] theorem ext {d : ℕ} {P Q : PolymerSupport d}
    (h : ∀ x : Site d, x ∈ P ↔ x ∈ Q) : P = Q := by
  cases P with
  | mk Pc =>
    cases Q with
    | mk Qc =>
      congr
      ext x
      exact h x


def empty (d : ℕ) : PolymerSupport d where
  carrier := ∅

@[simp] theorem not_mem_empty {d : ℕ} (x : Site d) :
    x ∉ empty d := by
  simp [empty]


def union {d : ℕ} (P Q : PolymerSupport d) : PolymerSupport d where
  carrier := P.carrier ∪ Q.carrier

instance {d : ℕ} : Union (PolymerSupport d) where
  union := PolymerSupport.union

@[simp] theorem union_carrier {d : ℕ} (P Q : PolymerSupport d) :
    (P ∪ Q).carrier = P.carrier ∪ Q.carrier :=
  rfl

@[simp] theorem mem_union {d : ℕ} (P Q : PolymerSupport d) (x : Site d) :
    x ∈ P ∪ Q ↔ x ∈ P ∨ x ∈ Q := by
  change x ∈ P.carrier ∪ Q.carrier ↔ x ∈ P.carrier ∨ x ∈ Q.carrier
  exact Finset.mem_union

@[simp] theorem empty_union {d : ℕ} (P : PolymerSupport d) :
    empty d ∪ P = P := by
  ext x
  simp [empty]

@[simp] theorem union_empty {d : ℕ} (P : PolymerSupport d) :
    P ∪ empty d = P := by
  ext x
  simp [empty]


def translate {d : ℕ} (P : PolymerSupport d) (v : Site d) : PolymerSupport d where
  carrier := P.carrier.image (fun x => x + v)

@[simp] theorem mem_translate {d : ℕ} (P : PolymerSupport d) (v x : Site d) :
    x ∈ P.translate v ↔ ∃ y, y ∈ P ∧ y + v = x := by
  classical
  change x ∈ P.carrier.image (fun y => y + v) ↔
    ∃ y, y ∈ P.carrier ∧ y + v = x
  exact Finset.mem_image

theorem mem_translate_iff_sub_mem {d : ℕ} (P : PolymerSupport d) (v x : Site d) :
    x ∈ P.translate v ↔ x - v ∈ P := by
  constructor
  · intro hx
    rcases (mem_translate P v x).mp hx with ⟨y, hy, rfl⟩
    have h : y + v - v = y := by
      ext i
      simp
    simpa [h] using hy
  · intro hx
    rw [mem_translate]
    refine ⟨x - v, hx, ?_⟩
    ext i
    simp

@[simp] theorem empty_translate {d : ℕ} (v : Site d) :
    (empty d).translate v = empty d := by
  ext x
  simp [translate, empty]

@[simp] theorem translate_zero {d : ℕ} (P : PolymerSupport d) :
    P.translate (0 : Site d) = P := by
  ext x
  simp [translate]

@[simp] theorem translate_translate {d : ℕ} (P : PolymerSupport d) (v w : Site d) :
    (P.translate v).translate w = P.translate (v + w) := by
  ext x
  simp [translate, add_assoc]

@[simp] theorem translate_card {d : ℕ} (P : PolymerSupport d) (v : Site d) :
    (P.translate v).carrier.card = P.carrier.card := by
  change (P.carrier.image fun x => x + v).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier (by
    intro x y hxy
    ext i
    have hcoord : x i + v i = y i + v i := by
      simpa using congrFun hxy i
    exact add_right_cancel hcoord)


def permuteCoordinatesSite {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Site d) :
    Site d :=
  fun i => x (σ.symm i)

@[simp] theorem permuteCoordinatesSite_refl {d : ℕ} (x : Site d) :
    permuteCoordinatesSite (Equiv.refl (Fin d)) x = x := by
  rfl

@[simp] theorem permuteCoordinatesSite_trans {d : ℕ}
    (σ τ : Equiv.Perm (Fin d)) (x : Site d) :
    permuteCoordinatesSite τ (permuteCoordinatesSite σ x) =
      permuteCoordinatesSite (σ.trans τ) x := by
  rfl

theorem permuteCoordinatesSite_injective {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Function.Injective (permuteCoordinatesSite σ) := by
  intro x y hxy
  ext i
  have hcoord := congrFun hxy (σ i)
  simpa [permuteCoordinatesSite] using hcoord


def permuteCoordinates {d : ℕ} (P : PolymerSupport d)
    (σ : Equiv.Perm (Fin d)) : PolymerSupport d where
  carrier := P.carrier.image (permuteCoordinatesSite σ)

@[simp] theorem mem_permuteCoordinates {d : ℕ}
    (P : PolymerSupport d) (σ : Equiv.Perm (Fin d)) (x : Site d) :
    x ∈ P.permuteCoordinates σ ↔
      ∃ y, y ∈ P ∧ permuteCoordinatesSite σ y = x := by
  classical
  change x ∈ P.carrier.image (permuteCoordinatesSite σ) ↔
    ∃ y, y ∈ P.carrier ∧ permuteCoordinatesSite σ y = x
  exact Finset.mem_image

@[simp] theorem permuteCoordinates_refl {d : ℕ} (P : PolymerSupport d) :
    P.permuteCoordinates (Equiv.refl (Fin d)) = P := by
  ext x
  simp [permuteCoordinates]

@[simp] theorem permuteCoordinates_trans {d : ℕ}
    (P : PolymerSupport d) (σ τ : Equiv.Perm (Fin d)) :
    (P.permuteCoordinates σ).permuteCoordinates τ =
      P.permuteCoordinates (σ.trans τ) := by
  ext x
  constructor
  · intro hx
    rcases (mem_permuteCoordinates (P.permuteCoordinates σ) τ x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_permuteCoordinates P σ y).mp hy with ⟨z, hz, rfl⟩
    exact (mem_permuteCoordinates P (σ.trans τ)
      (permuteCoordinatesSite τ (permuteCoordinatesSite σ z))).mpr ⟨z, hz, rfl⟩
  · intro hx
    rcases (mem_permuteCoordinates P (σ.trans τ) x).mp hx with ⟨z, hz, rfl⟩
    exact (mem_permuteCoordinates (P.permuteCoordinates σ) τ
      (permuteCoordinatesSite (σ.trans τ) z)).mpr
      ⟨permuteCoordinatesSite σ z,
        (mem_permuteCoordinates P σ (permuteCoordinatesSite σ z)).mpr
          ⟨z, hz, rfl⟩,
        rfl⟩

@[simp] theorem permuteCoordinates_card {d : ℕ}
    (P : PolymerSupport d) (σ : Equiv.Perm (Fin d)) :
    (P.permuteCoordinates σ).carrier.card = P.carrier.card := by
  change (P.carrier.image (permuteCoordinatesSite σ)).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier
    (permuteCoordinatesSite_injective σ)


def coordinateRadiusBound {d : ℕ} (R : ℕ) (x : Site d) : Prop :=
  ∀ i, (x i).natAbs ≤ R



theorem coordinateRadiusBound_blockRemainder {d : ℕ}
    (scale : BlockScale) (x : Site d) :
    coordinateRadiusBound (scale.L - 1) (blockRemainder scale x) := by
  intro i
  exact Nat.le_pred_of_lt (blockRemainder_natAbs_lt_scale scale x i)

@[simp] theorem coordinateRadiusBound_iff_mem_box {d R : ℕ} {x : Site d} :
    coordinateRadiusBound R x ↔ x ∈ box d R :=
  Iff.rfl

theorem coordinateRadiusBound_mono {d R S : ℕ} {x : Site d}
    (hRS : R ≤ S) (hx : coordinateRadiusBound R x) :
    coordinateRadiusBound S x := by
  intro i
  exact le_trans (hx i) hRS

theorem coordinateRadiusBound_add {d R S : ℕ} {x y : Site d}
    (hx : coordinateRadiusBound R x) (hy : coordinateRadiusBound S y) :
    coordinateRadiusBound (R + S) (x + y) := by
  intro i
  exact le_trans (Int.natAbs_add_le (x i) (y i))
    (Nat.add_le_add (hx i) (hy i))


theorem coordinateRadiusBound_permuteCoordinatesSite {d R : ℕ}
    {x : Site d} (σ : Equiv.Perm (Fin d))
    (hx : coordinateRadiusBound R x) :
    coordinateRadiusBound R (permuteCoordinatesSite σ x) := by
  intro i
  exact hx (σ.symm i)


def containedInBox {d : ℕ} (P : PolymerSupport d) (R : ℕ) : Prop :=
  ∀ x ∈ P, coordinateRadiusBound R x

theorem containedInBox_iff {d R : ℕ} {P : PolymerSupport d} :
    P.containedInBox R ↔ ∀ x ∈ P, x ∈ box d R :=
  Iff.rfl

@[simp] theorem containedInBox_empty {d R : ℕ} :
    (empty d).containedInBox R := by
  intro x hx
  exact False.elim ((not_mem_empty x) hx)

theorem containedInBox_mono_radius {d R S : ℕ} {P : PolymerSupport d}
    (hRS : R ≤ S) (hP : P.containedInBox R) :
    P.containedInBox S := by
  intro x hx
  exact coordinateRadiusBound_mono hRS (hP x hx)

theorem containedInBox_mono_support {d R : ℕ} {P Q : PolymerSupport d}
    (hPQ : ∀ {x : Site d}, x ∈ P → x ∈ Q) (hQ : Q.containedInBox R) :
    P.containedInBox R := by
  intro x hx
  exact hQ x (hPQ hx)

theorem containedInBox_translate {d R S : ℕ} {P : PolymerSupport d} {v : Site d}
    (hP : P.containedInBox R) (hv : coordinateRadiusBound S v) :
    (P.translate v).containedInBox (R + S) := by
  intro x hx
  rcases (mem_translate P v x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_add (hP y hy) hv


theorem containedInBox_permuteCoordinates {d R : ℕ} {P : PolymerSupport d}
    (σ : Equiv.Perm (Fin d)) (hP : P.containedInBox R) :
    (P.permuteCoordinates σ).containedInBox R := by
  intro x hx
  rcases (mem_permuteCoordinates P σ x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_permuteCoordinatesSite σ (hP y hy)



abbrev CoordinateReflection (d : ℕ) : Type :=
  Fin d → Bool


def reflectCoordinatesSite {d : ℕ} (ε : CoordinateReflection d) (x : Site d) :
    Site d :=
  fun i => if ε i then -x i else x i

@[simp] theorem reflectCoordinatesSite_false {d : ℕ} (x : Site d) :
    reflectCoordinatesSite (fun _ : Fin d => false) x = x := by
  ext i
  simp [reflectCoordinatesSite]

@[simp] theorem reflectCoordinatesSite_reflectCoordinatesSite {d : ℕ}
    (ε δ : CoordinateReflection d) (x : Site d) :
    reflectCoordinatesSite δ (reflectCoordinatesSite ε x) =
      reflectCoordinatesSite (fun i => Bool.xor (ε i) (δ i)) x := by
  ext i
  by_cases hε : ε i <;> by_cases hδ : δ i <;>
    simp [reflectCoordinatesSite, hε, hδ, Bool.xor]

theorem reflectCoordinatesSite_injective {d : ℕ} (ε : CoordinateReflection d) :
    Function.Injective (reflectCoordinatesSite ε) := by
  intro x y hxy
  ext i
  have hcoord := congrFun hxy i
  by_cases hε : ε i
  · have hneg := congrArg Neg.neg hcoord
    simpa [reflectCoordinatesSite, hε] using hneg
  · simpa [reflectCoordinatesSite, hε] using hcoord


def reflectCoordinates {d : ℕ} (P : PolymerSupport d)
    (ε : CoordinateReflection d) : PolymerSupport d where
  carrier := P.carrier.image (reflectCoordinatesSite ε)

@[simp] theorem mem_reflectCoordinates {d : ℕ}
    (P : PolymerSupport d) (ε : CoordinateReflection d) (x : Site d) :
    x ∈ P.reflectCoordinates ε ↔
      ∃ y, y ∈ P ∧ reflectCoordinatesSite ε y = x := by
  classical
  change x ∈ P.carrier.image (reflectCoordinatesSite ε) ↔
    ∃ y, y ∈ P.carrier ∧ reflectCoordinatesSite ε y = x
  exact Finset.mem_image

@[simp] theorem reflectCoordinates_false {d : ℕ} (P : PolymerSupport d) :
    P.reflectCoordinates (fun _ : Fin d => false) = P := by
  ext x
  simp [reflectCoordinates]

@[simp] theorem reflectCoordinates_reflectCoordinates {d : ℕ}
    (P : PolymerSupport d) (ε δ : CoordinateReflection d) :
    (P.reflectCoordinates ε).reflectCoordinates δ =
      P.reflectCoordinates (fun i => Bool.xor (ε i) (δ i)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_reflectCoordinates (P.reflectCoordinates ε) δ x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_reflectCoordinates P ε y).mp hy with ⟨z, hz, rfl⟩
    exact (mem_reflectCoordinates P (fun i => Bool.xor (ε i) (δ i))
      (reflectCoordinatesSite δ (reflectCoordinatesSite ε z))).mpr
      ⟨z, hz, (reflectCoordinatesSite_reflectCoordinatesSite ε δ z).symm⟩
  · intro hx
    rcases (mem_reflectCoordinates P (fun i => Bool.xor (ε i) (δ i)) x).mp hx with
      ⟨z, hz, rfl⟩
    exact (mem_reflectCoordinates (P.reflectCoordinates ε) δ
      (reflectCoordinatesSite (fun i => Bool.xor (ε i) (δ i)) z)).mpr
      ⟨reflectCoordinatesSite ε z,
        (mem_reflectCoordinates P ε (reflectCoordinatesSite ε z)).mpr
          ⟨z, hz, rfl⟩,
        reflectCoordinatesSite_reflectCoordinatesSite ε δ z⟩

@[simp] theorem reflectCoordinates_card {d : ℕ}
    (P : PolymerSupport d) (ε : CoordinateReflection d) :
    (P.reflectCoordinates ε).carrier.card = P.carrier.card := by
  change (P.carrier.image (reflectCoordinatesSite ε)).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier
    (reflectCoordinatesSite_injective ε)


theorem coordinateRadiusBound_reflectCoordinatesSite {d R : ℕ}
    {x : Site d} (ε : CoordinateReflection d)
    (hx : coordinateRadiusBound R x) :
    coordinateRadiusBound R (reflectCoordinatesSite ε x) := by
  intro i
  by_cases hε : ε i
  · simpa [reflectCoordinatesSite, hε] using hx i
  · simpa [reflectCoordinatesSite, hε] using hx i


theorem containedInBox_reflectCoordinates {d R : ℕ} {P : PolymerSupport d}
    (ε : CoordinateReflection d) (hP : P.containedInBox R) :
    (P.reflectCoordinates ε).containedInBox R := by
  intro x hx
  rcases (mem_reflectCoordinates P ε x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_reflectCoordinatesSite ε (hP y hy)



def cubicTransformSite {d : ℕ} (v : Site d) (σ : Equiv.Perm (Fin d))
    (ε : CoordinateReflection d) (x : Site d) : Site d :=
  reflectCoordinatesSite ε (permuteCoordinatesSite σ x) + v

@[simp] theorem cubicTransformSite_identity {d : ℕ} (x : Site d) :
    cubicTransformSite (0 : Site d) (Equiv.refl (Fin d))
      (fun _ : Fin d => false) x = x := by
  ext i
  simp [cubicTransformSite]

@[simp] theorem cubicTransformSite_comp {d : ℕ}
    (v w : Site d) (σ τ : Equiv.Perm (Fin d))
    (ε δ : CoordinateReflection d) (x : Site d) :
    cubicTransformSite w τ δ (cubicTransformSite v σ ε x) =
      cubicTransformSite
        (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) x := by
  ext i
  by_cases hε : ε (τ.symm i) <;> by_cases hδ : δ i <;>
    simp [cubicTransformSite, reflectCoordinatesSite, permuteCoordinatesSite,
      hε, hδ, Bool.xor] <;>
    ring

theorem cubicTransformSite_injective {d : ℕ} (v : Site d)
    (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d) :
    Function.Injective (cubicTransformSite v σ ε) := by
  intro x y hxy
  have hreflect :
      reflectCoordinatesSite ε (permuteCoordinatesSite σ x) =
        reflectCoordinatesSite ε (permuteCoordinatesSite σ y) := by
    ext i
    have hcoord :
        (reflectCoordinatesSite ε (permuteCoordinatesSite σ x)) i + v i =
          (reflectCoordinatesSite ε (permuteCoordinatesSite σ y)) i + v i := by
      simpa [cubicTransformSite] using congrFun hxy i
    exact add_right_cancel hcoord
  exact permuteCoordinatesSite_injective σ
    (reflectCoordinatesSite_injective ε hreflect)


def cubicInverseTranslation {d : ℕ} (v : Site d) (σ : Equiv.Perm (Fin d))
    (ε : CoordinateReflection d) : Site d :=
  -reflectCoordinatesSite (fun i => ε (σ i)) (permuteCoordinatesSite σ.symm v)


def cubicTransform {d : ℕ} (P : PolymerSupport d) (v : Site d)
    (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d) :
    PolymerSupport d where
  carrier := P.carrier.image (cubicTransformSite v σ ε)

@[simp] theorem mem_cubicTransform {d : ℕ}
    (P : PolymerSupport d) (v : Site d) (σ : Equiv.Perm (Fin d))
    (ε : CoordinateReflection d) (x : Site d) :
    x ∈ P.cubicTransform v σ ε ↔
      ∃ y, y ∈ P ∧ cubicTransformSite v σ ε y = x := by
  classical
  change x ∈ P.carrier.image (cubicTransformSite v σ ε) ↔
    ∃ y, y ∈ P.carrier ∧ cubicTransformSite v σ ε y = x
  exact Finset.mem_image

@[simp] theorem cubicTransform_card {d : ℕ} (P : PolymerSupport d)
    (v : Site d) (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d) :
    (P.cubicTransform v σ ε).carrier.card = P.carrier.card := by
  change (P.carrier.image (cubicTransformSite v σ ε)).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier
    (cubicTransformSite_injective v σ ε)

@[simp] theorem cubicTransform_identity {d : ℕ} (P : PolymerSupport d) :
    P.cubicTransform (0 : Site d) (Equiv.refl (Fin d))
      (fun _ : Fin d => false) = P := by
  ext x
  simp [cubicTransform]

@[simp] theorem cubicTransform_cubicTransform {d : ℕ}
    (P : PolymerSupport d) (v w : Site d) (σ τ : Equiv.Perm (Fin d))
    (ε δ : CoordinateReflection d) :
    (P.cubicTransform v σ ε).cubicTransform w τ δ =
      P.cubicTransform
        (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_cubicTransform (P.cubicTransform v σ ε) w τ δ x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_cubicTransform P v σ ε y).mp hy with ⟨z, hz, rfl⟩
    exact (mem_cubicTransform P
      (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
      (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i))
      (cubicTransformSite w τ δ (cubicTransformSite v σ ε z))).mpr
      ⟨z, hz, (cubicTransformSite_comp v w σ τ ε δ z).symm⟩
  · intro hx
    rcases (mem_cubicTransform P
      (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
      (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) x).mp hx with
      ⟨z, hz, rfl⟩
    exact (mem_cubicTransform (P.cubicTransform v σ ε) w τ δ
      (cubicTransformSite
        (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) z)).mpr
      ⟨cubicTransformSite v σ ε z,
        (mem_cubicTransform P v σ ε (cubicTransformSite v σ ε z)).mpr
          ⟨z, hz, rfl⟩,
        cubicTransformSite_comp v w σ τ ε δ z⟩

@[simp] theorem cubicTransform_inverse {d : ℕ}
    (P : PolymerSupport d) (v : Site d) (σ : Equiv.Perm (Fin d))
    (ε : CoordinateReflection d) :
    (P.cubicTransform v σ ε).cubicTransform
      (cubicInverseTranslation v σ ε) σ.symm (fun i => ε (σ i)) = P := by
  rw [cubicTransform_cubicTransform]
  have hsign :
      (fun i : Fin d => Bool.xor (ε (σ.symm.symm i)) ((fun i => ε (σ i)) i)) =
        (fun _ : Fin d => false) := by
    funext i
    by_cases hε : ε (σ i) <;>
      simp [hε, Bool.xor]
  rw [hsign]
  simp [cubicInverseTranslation]



theorem containedInBox_cubicTransform {d R S : ℕ} {P : PolymerSupport d}
    {v : Site d} (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d)
    (hP : P.containedInBox R) (hv : coordinateRadiusBound S v) :
    (P.cubicTransform v σ ε).containedInBox (R + S) := by
  intro x hx
  rcases (mem_cubicTransform P v σ ε x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_add
    (coordinateRadiusBound_reflectCoordinatesSite ε
      (coordinateRadiusBound_permuteCoordinatesSite σ (hP y hy))) hv

theorem containedInBox_union {d R : ℕ} (P Q : PolymerSupport d) :
    (P ∪ Q).containedInBox R ↔ P.containedInBox R ∧ Q.containedInBox R := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x ((mem_union P Q x).mpr (Or.inl hx))
    · intro x hx
      exact h x ((mem_union P Q x).mpr (Or.inr hx))
  · rintro ⟨hP, hQ⟩ x hx
    rcases (mem_union P Q x).mp hx with hxP | hxQ
    · exact hP x hxP
    · exact hQ x hxQ

theorem containedInBox_union_intro {d R : ℕ} {P Q : PolymerSupport d}
    (hP : P.containedInBox R) (hQ : Q.containedInBox R) :
    (P ∪ Q).containedInBox R :=
  (containedInBox_union P Q).mpr ⟨hP, hQ⟩


def coordinateDiameterBound {d : ℕ} (P : PolymerSupport d) (R : ℕ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ∀ i, (x i - y i).natAbs ≤ R

@[simp] theorem coordinateDiameterBound_empty {d R : ℕ} :
    (empty d).coordinateDiameterBound R := by
  intro x hx
  exact False.elim ((not_mem_empty x) hx)

theorem coordinateDiameterBound_mono_radius {d R S : ℕ} {P : PolymerSupport d}
    (hRS : R ≤ S) (hP : P.coordinateDiameterBound R) :
    P.coordinateDiameterBound S := by
  intro x hx y hy i
  exact le_trans (hP x hx y hy i) hRS

theorem coordinateDiameterBound_mono_support {d R : ℕ} {P Q : PolymerSupport d}
    (hPQ : ∀ {x : Site d}, x ∈ P → x ∈ Q) (hQ : Q.coordinateDiameterBound R) :
    P.coordinateDiameterBound R := by
  intro x hx y hy i
  exact hQ x (hPQ hx) y (hPQ hy) i

theorem coordinateDiameterBound_of_containedInBox {d R : ℕ} {P : PolymerSupport d}
    (hP : P.containedInBox R) :
    P.coordinateDiameterBound (R + R) := by
  intro x hx y hy i
  exact le_trans (Int.natAbs_sub_le (x i) (y i))
    (Nat.add_le_add (hP x hx i) (hP y hy i))

theorem coordinateDiameterBound_translate {d R : ℕ} {P : PolymerSupport d} {v : Site d}
    (hP : P.coordinateDiameterBound R) :
    (P.translate v).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_translate P v x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_translate P v y).mp hy with ⟨y₀, hy₀, rfl⟩
  have hcoord : (x₀ + v) i - (y₀ + v) i = x₀ i - y₀ i := by
    change (x₀ i + v i) - (y₀ i + v i) = x₀ i - y₀ i
    ring
  rw [hcoord]
  exact hP x₀ hx₀ y₀ hy₀ i



theorem containedInBox_translate_neg_of_mem_of_coordinateDiameterBound
    {d R : ℕ} {P : PolymerSupport d} {a : Site d}
    (ha : a ∈ P) (hP : P.coordinateDiameterBound R) :
    (P.translate (-a)).containedInBox R := by
  intro x hx i
  rcases (mem_translate P (-a) x).mp hx with ⟨y, hy, rfl⟩
  have hcoord : (y + -a) i = y i - a i := by
    simp
    ring
  rw [hcoord]
  exact hP y hy a ha i



theorem exists_translate_containedInBox_of_nonempty_coordinateDiameterBound
    {d R : ℕ} {P : PolymerSupport d}
    (hne : P.carrier.Nonempty) (hP : P.coordinateDiameterBound R) :
    ∃ v : Site d, (P.translate v).containedInBox R := by
  rcases hne with ⟨a, ha⟩
  exact ⟨-a,
    containedInBox_translate_neg_of_mem_of_coordinateDiameterBound ha hP⟩


theorem coordinateDiameterBound_permuteCoordinates {d R : ℕ}
    {P : PolymerSupport d} (σ : Equiv.Perm (Fin d))
    (hP : P.coordinateDiameterBound R) :
    (P.permuteCoordinates σ).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_permuteCoordinates P σ x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_permuteCoordinates P σ y).mp hy with ⟨y₀, hy₀, rfl⟩
  exact hP x₀ hx₀ y₀ hy₀ (σ.symm i)


theorem coordinateDiameterBound_reflectCoordinates {d R : ℕ}
    {P : PolymerSupport d} (ε : CoordinateReflection d)
    (hP : P.coordinateDiameterBound R) :
    (P.reflectCoordinates ε).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_reflectCoordinates P ε x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_reflectCoordinates P ε y).mp hy with ⟨y₀, hy₀, rfl⟩
  by_cases hε : ε i
  · have hcoord :
        reflectCoordinatesSite ε x₀ i - reflectCoordinatesSite ε y₀ i =
          -(x₀ i - y₀ i) := by
      simp [reflectCoordinatesSite, hε]
      ring
    rw [hcoord, Int.natAbs_neg]
    exact hP x₀ hx₀ y₀ hy₀ i
  · simpa [reflectCoordinatesSite, hε] using hP x₀ hx₀ y₀ hy₀ i




theorem coordinateDiameterBound_cubicTransform {d R : ℕ}
    {P : PolymerSupport d} {v : Site d}
    (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d)
    (hP : P.coordinateDiameterBound R) :
    (P.cubicTransform v σ ε).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_cubicTransform P v σ ε x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_cubicTransform P v σ ε y).mp hy with ⟨y₀, hy₀, rfl⟩
  have hbase := hP x₀ hx₀ y₀ hy₀ (σ.symm i)
  by_cases hε : ε i
  · have hcoord :
        cubicTransformSite v σ ε x₀ i -
            cubicTransformSite v σ ε y₀ i =
          -(x₀ (σ.symm i) - y₀ (σ.symm i)) := by
      simp [cubicTransformSite, reflectCoordinatesSite,
        permuteCoordinatesSite, hε]
      ring
    rw [hcoord, Int.natAbs_neg]
    exact hbase
  · have hcoord :
        cubicTransformSite v σ ε x₀ i -
            cubicTransformSite v σ ε y₀ i =
          x₀ (σ.symm i) - y₀ (σ.symm i) := by
      simp [cubicTransformSite, reflectCoordinatesSite,
        permuteCoordinatesSite, hε]
    rw [hcoord]
    exact hbase

theorem coordinateDiameterBound_union {d R : ℕ} {P Q : PolymerSupport d}
    (hP : P.coordinateDiameterBound R) (hQ : Q.coordinateDiameterBound R)
    (hCross : ∀ x ∈ P, ∀ y ∈ Q, ∀ i, (x i - y i).natAbs ≤ R) :
    (P ∪ Q).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_union P Q x).mp hx with hxP | hxQ
  · rcases (mem_union P Q y).mp hy with hyP | hyQ
    · exact hP x hxP y hyP i
    · exact hCross x hxP y hyQ i
  · rcases (mem_union P Q y).mp hy with hyP | hyQ
    · have hsym : (x i - y i).natAbs = (y i - x i).natAbs := by
        have hneg : x i - y i = -(y i - x i) := by ring
        rw [hneg, Int.natAbs_neg]
      simpa [hsym] using hCross y hyP x hxQ i
    · exact hQ x hxQ y hyQ i

theorem coordinateDiameterBound_union_of_containedInBox {d R : ℕ}
    {P Q : PolymerSupport d} (hP : P.containedInBox R) (hQ : Q.containedInBox R) :
    (P ∪ Q).coordinateDiameterBound (R + R) :=
  coordinateDiameterBound_of_containedInBox (containedInBox_union_intro hP hQ)

end PolymerSupport


structure PolymerSymmetryTag where
  translationQuotiented : Bool
  cubicQuotiented : Bool
  spinFlipEven : Bool


structure LocalPolymerCoordinate (d : ℕ) where
  support : PolymerSupport d
  degree : ℕ
  range : ℕ
  symmetry : PolymerSymmetryTag



structure LatticeRGData (d : ℕ) where
  H : EffectiveHamiltonian
  R : BlockSpinMap H
  kernel : BlockSpinKernel d
  scale_match : kernel.scale = R.scale

namespace LatticeRGData

variable {d : ℕ}

@[simp] theorem kernel_scale_eq_R_scale (G : LatticeRGData d) :
    G.kernel.scale = G.R.scale :=
  G.scale_match

theorem R_scale_eq_kernel_scale (G : LatticeRGData d) :
    G.R.scale = G.kernel.scale :=
  G.scale_match.symm

@[simp] theorem kernel_scale_toReal_eq_R_scale_toReal
    (G : LatticeRGData d) :
    G.kernel.scale.toReal = G.R.scale.toReal := by
  exact congrArg BlockScale.toReal G.kernel_scale_eq_R_scale

theorem R_scale_toReal_eq_kernel_scale_toReal
    (G : LatticeRGData d) :
    G.R.scale.toReal = G.kernel.scale.toReal := by
  exact congrArg BlockScale.toReal G.R_scale_eq_kernel_scale

end LatticeRGData

end Exact3D
end StatMech
