/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.LatticeRG
import Code.Exact3D.Intervals









namespace StatMech
namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace PolymerSupport

instance instDecidableEq (d : ℕ) : DecidableEq (PolymerSupport d) := by
  intro P Q
  cases P with
  | mk Pc =>
    cases Q with
    | mk Qc =>
      by_cases h : Pc = Qc
      · exact isTrue (by cases h; rfl)
      · exact isFalse (by intro hPQ; cases hPQ; exact h rfl)





def translationCandidateSet {d : ℕ} (P Q : PolymerSupport d) :
    Finset (Site d) :=
  Q.carrier.biUnion fun y => P.carrier.image fun x => y - x

@[simp] theorem mem_translationCandidateSet {d : ℕ}
    (P Q : PolymerSupport d) (v : Site d) :
    v ∈ translationCandidateSet P Q ↔
      ∃ y, y ∈ Q ∧ ∃ x, x ∈ P ∧ y - x = v := by
  classical
  simp [translationCandidateSet]




def finiteTranslationEquivalent {d : ℕ} (P Q : PolymerSupport d) : Prop :=
  (P.carrier = ∅ ∧ Q.carrier = ∅) ∨
    ∃ v : {v : Site d // v ∈ translationCandidateSet P Q},
      Q = P.translate v.1

instance finiteTranslationEquivalentDecidable {d : ℕ} (P Q : PolymerSupport d) :
    Decidable (finiteTranslationEquivalent P Q) := by
  unfold finiteTranslationEquivalent
  infer_instance

theorem finiteTranslationEquivalent_iff {d : ℕ} (P Q : PolymerSupport d) :
    finiteTranslationEquivalent P Q ↔ ∃ v : Site d, Q = P.translate v := by
  classical
  constructor
  · intro h
    rcases h with ⟨hP, hQ⟩ | ⟨v, htrans⟩
    · refine ⟨0, ?_⟩
      ext x
      simp [translate, hP, hQ]
    · exact ⟨v.1, htrans⟩
  · rintro ⟨v, htrans⟩
    by_cases hP : P.carrier = ∅
    · left
      refine ⟨hP, ?_⟩
      ext x
      simp [htrans, translate, hP]
    · right
      have hnonempty : P.carrier.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hP
      rcases hnonempty with ⟨x, hx⟩
      have hy : x + v ∈ Q := by
        rw [htrans]
        exact (mem_translate P v (x + v)).mpr ⟨x, hx, rfl⟩
      have hv : x + v - x = v := by
        ext i
        simp
      refine ⟨⟨v, ?_⟩, htrans⟩
      exact (mem_translationCandidateSet P Q v).mpr
        ⟨x + v, hy, x, hx, hv⟩



theorem cubicTransform_zero_translate {d : ℕ} (P : PolymerSupport d)
    (v : Site d) (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d) :
    (P.cubicTransform (0 : Site d) σ ε).translate v =
      P.cubicTransform v σ ε := by
  ext x
  constructor
  · intro hx
    rcases (mem_translate (P.cubicTransform (0 : Site d) σ ε) v x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_cubicTransform P (0 : Site d) σ ε y).mp hy with
      ⟨z, hz, rfl⟩
    exact (mem_cubicTransform P v σ ε
      (cubicTransformSite (0 : Site d) σ ε z + v)).mpr
        ⟨z, hz, by simp [cubicTransformSite]⟩
  · intro hx
    rcases (mem_cubicTransform P v σ ε x).mp hx with ⟨z, hz, rfl⟩
    exact (mem_translate (P.cubicTransform (0 : Site d) σ ε) v
      (cubicTransformSite v σ ε z)).mpr
      ⟨cubicTransformSite (0 : Site d) σ ε z,
        (mem_cubicTransform P (0 : Site d) σ ε
          (cubicTransformSite (0 : Site d) σ ε z)).mpr ⟨z, hz, rfl⟩,
        by simp [cubicTransformSite]⟩

end PolymerSupport


abbrev BoundedSite (d R : ℕ) : Type :=
  {x : Site d // x ∈ box d R}

namespace BoundedSite

noncomputable instance instFintype (d R : ℕ) : Fintype (BoundedSite d R) :=
  (box_finite d R).fintype

instance instDecidableEq (d R : ℕ) : DecidableEq (BoundedSite d R) :=
  inferInstance


def val {d R : ℕ} (x : BoundedSite d R) : Site d :=
  x.1

@[simp] theorem val_mem_box {d R : ℕ} (x : BoundedSite d R) :
    val x ∈ box d R :=
  x.2


def coordinateList {d R : ℕ} (x : BoundedSite d R) : List ℤ :=
  List.ofFn x.1

theorem coordinateList_injective {d R : ℕ} :
    Function.Injective (@coordinateList d R) := by
  intro x y h
  exact Subtype.ext (List.ofFn_inj.mp h)


def coordinateEmbedding (d R : ℕ) : BoundedSite d R ↪ List ℤ where
  toFun := coordinateList
  inj' := coordinateList_injective

end BoundedSite



structure BoundedPolymerCase (d R maxDegree maxRange : ℕ) where
  support : Finset (BoundedSite d R)
  degree : Fin (maxDegree + 1)
  range : Fin (maxRange + 1)
deriving DecidableEq, Fintype

namespace BoundedPolymerCase



abbrev StableKey (maxDegree maxRange : ℕ) : Type :=
  List (List ℤ) ×ₗ (Fin (maxDegree + 1) ×ₗ Fin (maxRange + 1))


def supportKey {d R : ℕ} (s : Finset (BoundedSite d R)) : List (List ℤ) :=
  (s.map (BoundedSite.coordinateEmbedding d R)).sort

theorem supportKey_toFinset {d R : ℕ} (s : Finset (BoundedSite d R)) :
    (supportKey s).toFinset = s.map (BoundedSite.coordinateEmbedding d R) := by
  simp [supportKey]

theorem supportKey_injective {d R : ℕ} :
    Function.Injective (@supportKey d R) := by
  intro s t h
  apply Finset.map_inj.mp
  calc
    s.map (BoundedSite.coordinateEmbedding d R) = (supportKey s).toFinset :=
      (supportKey_toFinset s).symm
    _ = (supportKey t).toFinset := by rw [h]
    _ = t.map (BoundedSite.coordinateEmbedding d R) :=
      supportKey_toFinset t


def stableKey {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    StableKey maxDegree maxRange :=
  toLex (supportKey c.support, toLex (c.degree, c.range))

theorem stableKey_injective {d R maxDegree maxRange : ℕ} :
    Function.Injective (@stableKey d R maxDegree maxRange) := by
  intro c c' h
  have hpair :
      (supportKey c.support, toLex (c.degree, c.range)) =
        (supportKey c'.support, toLex (c'.degree, c'.range)) := by
    simpa [stableKey] using congrArg ofLex h
  have hsuppKey : supportKey c.support = supportKey c'.support :=
    congrArg Prod.fst hpair
  have hdegRangeLex : toLex (c.degree, c.range) = toLex (c'.degree, c'.range) :=
    congrArg Prod.snd hpair
  have hdegRange : (c.degree, c.range) = (c'.degree, c'.range) := by
    simpa using congrArg ofLex hdegRangeLex
  cases c
  cases c'
  simp only at hsuppKey hdegRange ⊢
  have hsupp := supportKey_injective hsuppKey
  cases hdegRange
  cases hsupp
  rfl



@[reducible] noncomputable def stableLinearOrder
    (d R maxDegree maxRange : ℕ) :
    LinearOrder (BoundedPolymerCase d R maxDegree maxRange) :=
  LinearOrder.lift' stableKey stableKey_injective

noncomputable instance instLinearOrder (d R maxDegree maxRange : ℕ) :
    LinearOrder (BoundedPolymerCase d R maxDegree maxRange) :=
  stableLinearOrder d R maxDegree maxRange


noncomputable def boundedSupportOf {d R : ℕ} (P : PolymerSupport d)
    (hP : P.containedInBox R) : Finset (BoundedSite d R) :=
  P.carrier.attach.image fun x => ⟨x.1, hP x.1 (by simp)⟩



theorem mem_boundedSupportOf {d R : ℕ} (P : PolymerSupport d)
    (hP : P.containedInBox R) (x : BoundedSite d R) :
    x ∈ boundedSupportOf P hP ↔ x.1 ∈ P := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hval : y.1 = x.1 := Subtype.ext_iff.mp hxy
    simpa [hval] using y.2
  · intro hx
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨x.1, by simpa using hx⟩, by simp, ?_⟩
    ext i
    rfl


theorem boundedSupportOf_card {d R : ℕ} (P : PolymerSupport d)
    (hP : P.containedInBox R) :
    (boundedSupportOf P hP).card = P.carrier.card := by
  classical
  unfold boundedSupportOf
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro x y hxy
    exact Subtype.ext (congrArg BoundedSite.val hxy)



noncomputable def ofLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    BoundedPolymerCase d R maxDegree maxRange where
  support := boundedSupportOf c.support hbox
  degree := ⟨c.degree, Nat.lt_succ_of_le hdegree⟩
  range := ⟨c.range, Nat.lt_succ_of_le hrange⟩


@[simp] theorem ofLocalCoordinate_support {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).support =
      boundedSupportOf c.support hbox :=
  rfl



@[simp] theorem mem_ofLocalCoordinate_support {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) (x : BoundedSite d R) :
    x ∈ (ofLocalCoordinate c hbox hdegree hrange).support ↔
      x.1 ∈ c.support := by
  simpa [ofLocalCoordinate] using mem_boundedSupportOf c.support hbox x


@[simp] theorem ofLocalCoordinate_degree_val {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinate c hbox hdegree hrange).degree : ℕ) = c.degree :=
  rfl


@[simp] theorem ofLocalCoordinate_range_val {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinate c hbox hdegree hrange).range : ℕ) = c.range :=
  rfl


theorem ofLocalCoordinate_support_card {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).support.card =
      c.support.carrier.card := by
  simpa [ofLocalCoordinate] using boundedSupportOf_card c.support hbox



abbrev BoundedLocalCoordinate (d R maxDegree maxRange : ℕ) : Type :=
  {c : LocalPolymerCoordinate d //
    c.support.containedInBox R ∧ c.degree ≤ maxDegree ∧ c.range ≤ maxRange}


noncomputable def classifyBoundedLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  ofLocalCoordinate c.1 c.2.1 c.2.2.1 c.2.2.2


@[simp] theorem classifyBoundedLocalCoordinate_degree_val
    {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    ((classifyBoundedLocalCoordinate c).degree : ℕ) = c.1.degree :=
  rfl


@[simp] theorem classifyBoundedLocalCoordinate_range_val
    {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    ((classifyBoundedLocalCoordinate c).range : ℕ) = c.1.range :=
  rfl


def toPolymerSupport {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) : PolymerSupport d where
  carrier := c.support.image BoundedSite.val



theorem mem_toPolymerSupport {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) (x : Site d) :
    x ∈ c.toPolymerSupport ↔
      ∃ y, y ∈ c.support ∧ BoundedSite.val y = x := by
  classical
  change x ∈ c.support.image BoundedSite.val ↔
    ∃ y, y ∈ c.support ∧ BoundedSite.val y = x
  exact Finset.mem_image



@[simp] theorem boundedSite_val_mem_toPolymerSupport
    {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) (x : BoundedSite d R) :
    BoundedSite.val x ∈ c.toPolymerSupport ↔ x ∈ c.support := by
  constructor
  · intro hx
    rcases (mem_toPolymerSupport c (BoundedSite.val x)).mp hx with
      ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    exact (mem_toPolymerSupport c (BoundedSite.val x)).mpr ⟨x, hx, rfl⟩



theorem toPolymerSupport_card {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c.toPolymerSupport.carrier.card = c.support.card := by
  classical
  unfold toPolymerSupport
  exact Finset.card_image_of_injective c.support (by
    intro x y hxy
    exact Subtype.ext hxy)


theorem toPolymerSupport_containedInBox {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c.toPolymerSupport.containedInBox R := by
  intro x hx
  classical
  change x ∈ c.support.image BoundedSite.val at hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  exact y.2



theorem toPolymerSupport_coordinateDiameterBound {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c.toPolymerSupport.coordinateDiameterBound (R + R) :=
  PolymerSupport.coordinateDiameterBound_of_containedInBox
    (toPolymerSupport_containedInBox c)



theorem toPolymerSupport_ofLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport = c.support := by
  ext x
  constructor
  · intro hx
    classical
    change x ∈ (boundedSupportOf c.support hbox).image BoundedSite.val at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hy' := (mem_boundedSupportOf c.support hbox y).mp hy
    simpa [BoundedSite.val] using hxy ▸ hy'
  · intro hx
    classical
    change x ∈ (boundedSupportOf c.support hbox).image BoundedSite.val
    refine Finset.mem_image.mpr ?_
    let y : BoundedSite d R := ⟨x, hbox x hx⟩
    refine ⟨y, ?_, rfl⟩
    exact (mem_boundedSupportOf c.support hbox y).mpr hx



@[simp] theorem mem_toPolymerSupport_ofLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) (x : Site d) :
    x ∈ (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport ↔
      x ∈ c.support := by
  rw [toPolymerSupport_ofLocalCoordinate]


theorem toPolymerSupport_ofLocalCoordinate_card {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport.carrier.card =
      c.support.carrier.card := by
  rw [toPolymerSupport_ofLocalCoordinate]



noncomputable def translateLocalCoordinate {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) : LocalPolymerCoordinate d where
  support := c.support.translate v
  degree := c.degree
  range := c.range
  symmetry := c.symmetry

@[simp] theorem translateLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).support = c.support.translate v :=
  rfl

@[simp] theorem translateLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).degree = c.degree :=
  rfl

@[simp] theorem translateLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).range = c.range :=
  rfl

@[simp] theorem translateLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry = c.symmetry :=
  rfl

@[simp] theorem translateLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem translateLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem translateLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem translateLocalCoordinate_zero {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    translateLocalCoordinate c (0 : Site d) = c := by
  cases c
  simp [translateLocalCoordinate]

@[simp] theorem translateLocalCoordinate_translate {d : ℕ}
    (c : LocalPolymerCoordinate d) (v w : Site d) :
    translateLocalCoordinate (translateLocalCoordinate c v) w =
      translateLocalCoordinate c (v + w) := by
  cases c
  simp [translateLocalCoordinate]

@[simp] theorem translateLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).support.carrier.card =
      c.support.carrier.card := by
  simp [translateLocalCoordinate]


theorem translateLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (hdiam : c.support.coordinateDiameterBound R) :
    (translateLocalCoordinate c v).support.coordinateDiameterBound R := by
  simpa [translateLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_translate (P := c.support)
      (v := v) hdiam



noncomputable def permuteLocalCoordinate {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (σ : Equiv.Perm (Fin d)) : LocalPolymerCoordinate d where
  support := c.support.permuteCoordinates σ
  degree := c.degree
  range := c.range
  symmetry := c.symmetry

@[simp] theorem permuteLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).support = c.support.permuteCoordinates σ :=
  rfl

@[simp] theorem permuteLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).degree = c.degree :=
  rfl

@[simp] theorem permuteLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).range = c.range :=
  rfl

@[simp] theorem permuteLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry = c.symmetry :=
  rfl

@[simp] theorem permuteLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem permuteLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem permuteLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem permuteLocalCoordinate_refl {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    permuteLocalCoordinate c (Equiv.refl (Fin d)) = c := by
  cases c
  simp [permuteLocalCoordinate]

@[simp] theorem permuteLocalCoordinate_trans {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ τ : Equiv.Perm (Fin d)) :
    permuteLocalCoordinate (permuteLocalCoordinate c σ) τ =
      permuteLocalCoordinate c (σ.trans τ) := by
  cases c
  simp [permuteLocalCoordinate]

@[simp] theorem permuteLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).support.carrier.card =
      c.support.carrier.card := by
  simp [permuteLocalCoordinate]


theorem permuteLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hdiam : c.support.coordinateDiameterBound R) :
    (permuteLocalCoordinate c σ).support.coordinateDiameterBound R := by
  simpa [permuteLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_permuteCoordinates
      (P := c.support) σ hdiam


theorem permuteLocalCoordinate_containedInBox {d R : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hbox : c.support.containedInBox R) :
    (permuteLocalCoordinate c σ).support.containedInBox R := by
  simpa [permuteLocalCoordinate] using
    PolymerSupport.containedInBox_permuteCoordinates
      (P := c.support) σ hbox



noncomputable def reflectLocalCoordinate {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    LocalPolymerCoordinate d where
  support := c.support.reflectCoordinates ε
  degree := c.degree
  range := c.range
  symmetry := c.symmetry

@[simp] theorem reflectLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).support = c.support.reflectCoordinates ε :=
  rfl

@[simp] theorem reflectLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).degree = c.degree :=
  rfl

@[simp] theorem reflectLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).range = c.range :=
  rfl

@[simp] theorem reflectLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry = c.symmetry :=
  rfl

@[simp] theorem reflectLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem reflectLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem reflectLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem reflectLocalCoordinate_false {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    reflectLocalCoordinate c (fun _ : Fin d => false) = c := by
  cases c
  simp [reflectLocalCoordinate]

@[simp] theorem reflectLocalCoordinate_reflectLocalCoordinate {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε δ : PolymerSupport.CoordinateReflection d) :
    reflectLocalCoordinate (reflectLocalCoordinate c ε) δ =
      reflectLocalCoordinate c (fun i => Bool.xor (ε i) (δ i)) := by
  cases c
  simp [reflectLocalCoordinate]

@[simp] theorem reflectLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).support.carrier.card =
      c.support.carrier.card := by
  simp [reflectLocalCoordinate]


theorem reflectLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hdiam : c.support.coordinateDiameterBound R) :
    (reflectLocalCoordinate c ε).support.coordinateDiameterBound R := by
  simpa [reflectLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_reflectCoordinates
      (P := c.support) ε hdiam


theorem reflectLocalCoordinate_containedInBox {d R : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R) :
    (reflectLocalCoordinate c ε).support.containedInBox R := by
  simpa [reflectLocalCoordinate] using
    PolymerSupport.containedInBox_reflectCoordinates
      (P := c.support) ε hbox



noncomputable def cubicTransformLocalCoordinate {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    LocalPolymerCoordinate d where
  support := c.support.cubicTransform v σ ε
  degree := c.degree
  range := c.range
  symmetry := c.symmetry

@[simp] theorem cubicTransformLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).support =
      c.support.cubicTransform v σ ε :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).degree = c.degree :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).range = c.range :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry = c.symmetry :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_identity {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    cubicTransformLocalCoordinate c (0 : Site d) (Equiv.refl (Fin d))
      (fun _ : Fin d => false) = c := by
  cases c
  simp [cubicTransformLocalCoordinate]

@[simp] theorem cubicTransformLocalCoordinate_cubicTransform {d : ℕ}
    (c : LocalPolymerCoordinate d) (v w : Site d)
    (σ τ : Equiv.Perm (Fin d))
    (ε δ : PolymerSupport.CoordinateReflection d) :
    cubicTransformLocalCoordinate
        (cubicTransformLocalCoordinate c v σ ε) w τ δ =
      cubicTransformLocalCoordinate c
        (PolymerSupport.reflectCoordinatesSite δ
          (PolymerSupport.permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
  cases c
  simp [cubicTransformLocalCoordinate]

@[simp] theorem cubicTransformLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).support.carrier.card =
      c.support.carrier.card := by
  simp [cubicTransformLocalCoordinate]


theorem cubicTransformLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hdiam : c.support.coordinateDiameterBound R) :
    (cubicTransformLocalCoordinate c v σ ε).support.coordinateDiameterBound R := by
  simpa [cubicTransformLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_cubicTransform
      (P := c.support) (v := v) σ ε hdiam



theorem cubicTransformLocalCoordinate_containedInBox {d R S : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hv : PolymerSupport.coordinateRadiusBound S v) :
    (cubicTransformLocalCoordinate c v σ ε).support.containedInBox
      (R + S) := by
  simpa [cubicTransformLocalCoordinate] using
    PolymerSupport.containedInBox_cubicTransform
      (P := c.support) (v := v) σ ε hbox hv



noncomputable def ofLocalCoordinateAnchoredAt {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  ofLocalCoordinate (translateLocalCoordinate c (-a))
    (by
      simpa [translateLocalCoordinate] using
        PolymerSupport.containedInBox_translate_neg_of_mem_of_coordinateDiameterBound
          ha hdiam)
    (by simpa [translateLocalCoordinate] using hdegree)
    (by simpa [translateLocalCoordinate] using hrange)

@[simp] theorem ofLocalCoordinateAnchoredAt_degree_val
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).degree : ℕ) =
      c.degree :=
  rfl

@[simp] theorem ofLocalCoordinateAnchoredAt_range_val
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).range : ℕ) =
      c.range :=
  rfl



theorem toPolymerSupport_ofLocalCoordinateAnchoredAt
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).toPolymerSupport =
      c.support.translate (-a) := by
  rw [ofLocalCoordinateAnchoredAt, toPolymerSupport_ofLocalCoordinate]
  rfl



theorem exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
        bc.toPolymerSupport = c.support.translate v := by
  rcases hne with ⟨a, ha⟩
  refine ⟨-a, ofLocalCoordinateAnchoredAt c (a := a) (by simpa using ha)
    hdiam hdegree hrange, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact toPolymerSupport_ofLocalCoordinateAnchoredAt c (by simpa using ha)
      hdiam hdegree hrange





def translationEquivalent {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) : Prop :=
  c.degree = c'.degree ∧ c.range = c'.range ∧
    ∃ v : Site d, c'.toPolymerSupport = c.toPolymerSupport.translate v

@[simp] theorem translationEquivalent_refl {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    translationEquivalent c c := by
  refine ⟨rfl, rfl, ⟨0, ?_⟩⟩
  simp

theorem translationEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : translationEquivalent c c') :
    translationEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, v, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm, ⟨-v, ?_⟩⟩
  have htranslated :
      c'.toPolymerSupport.translate (-v) = c.toPolymerSupport := by
    rw [hsupport, PolymerSupport.translate_translate]
    simp
  exact htranslated.symm

theorem translationEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : translationEquivalent c₁ c₂)
    (h₂₃ : translationEquivalent c₂ c₃) :
    translationEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, v, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, w, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃, ⟨v + w, ?_⟩⟩
  calc
    c₃.toPolymerSupport = c₂.toPolymerSupport.translate w := hsupport₂₃
    _ = (c₁.toPolymerSupport.translate v).translate w := by rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.translate (v + w) := by
      rw [PolymerSupport.translate_translate]


def translationSetoid (d R maxDegree maxRange : ℕ) :
    Setoid (BoundedPolymerCase d R maxDegree maxRange) where
  r := translationEquivalent
  iseqv := by
    constructor
    · intro c
      exact translationEquivalent_refl c
    · intro c c' h
      exact translationEquivalent_symm h
    · intro c₁ c₂ c₃ h₁₂ h₂₃
      exact translationEquivalent_trans h₁₂ h₂₃




abbrev TranslationClass (d R maxDegree maxRange : ℕ) : Type :=
  Quotient (translationSetoid d R maxDegree maxRange)



noncomputable instance translationClassFintype (d R maxDegree maxRange : ℕ) :
    Fintype (TranslationClass d R maxDegree maxRange) := by
  classical
  unfold TranslationClass
  infer_instance


def translationClass {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    TranslationClass d R maxDegree maxRange :=
  Quotient.mk (translationSetoid d R maxDegree maxRange) c


noncomputable def exhaustiveTranslationClassTable
    (d R maxDegree maxRange : ℕ) :
    Finset (TranslationClass d R maxDegree maxRange) :=
  Finset.univ



theorem exhaustiveTranslationClassTable_covers
    (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    translationClass c ∈
      exhaustiveTranslationClassTable d R maxDegree maxRange := by
  classical
  simp [exhaustiveTranslationClassTable]




def coordinatePermutationEquivalent {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) : Prop :=
  c.degree = c'.degree ∧ c.range = c'.range ∧
    ∃ σ : Equiv.Perm (Fin d),
      c'.toPolymerSupport = c.toPolymerSupport.permuteCoordinates σ

@[simp] theorem coordinatePermutationEquivalent_refl
    {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    coordinatePermutationEquivalent c c := by
  refine ⟨rfl, rfl, ⟨Equiv.refl (Fin d), ?_⟩⟩
  simp

theorem coordinatePermutationEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : coordinatePermutationEquivalent c c') :
    coordinatePermutationEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, σ, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm, ⟨σ.symm, ?_⟩⟩
  have hpermuted :
      c'.toPolymerSupport.permuteCoordinates σ.symm =
        c.toPolymerSupport := by
    rw [hsupport, PolymerSupport.permuteCoordinates_trans]
    simp
  exact hpermuted.symm

theorem coordinatePermutationEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : coordinatePermutationEquivalent c₁ c₂)
    (h₂₃ : coordinatePermutationEquivalent c₂ c₃) :
    coordinatePermutationEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, σ, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, τ, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃,
    ⟨σ.trans τ, ?_⟩⟩
  calc
    c₃.toPolymerSupport = c₂.toPolymerSupport.permuteCoordinates τ := hsupport₂₃
    _ = (c₁.toPolymerSupport.permuteCoordinates σ).permuteCoordinates τ := by
      rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.permuteCoordinates (σ.trans τ) := by
      rw [PolymerSupport.permuteCoordinates_trans]


def coordinatePermutationSetoid (d R maxDegree maxRange : ℕ) :
    Setoid (BoundedPolymerCase d R maxDegree maxRange) where
  r := coordinatePermutationEquivalent
  iseqv := by
    constructor
    · intro c
      exact coordinatePermutationEquivalent_refl c
    · intro c c' h
      exact coordinatePermutationEquivalent_symm h
    · intro c₁ c₂ c₃ h₁₂ h₂₃
      exact coordinatePermutationEquivalent_trans h₁₂ h₂₃


abbrev CoordinatePermutationClass (d R maxDegree maxRange : ℕ) : Type :=
  Quotient (coordinatePermutationSetoid d R maxDegree maxRange)



noncomputable instance coordinatePermutationClassFintype
    (d R maxDegree maxRange : ℕ) :
    Fintype (CoordinatePermutationClass d R maxDegree maxRange) := by
  classical
  unfold CoordinatePermutationClass
  infer_instance


def coordinatePermutationClass {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    CoordinatePermutationClass d R maxDegree maxRange :=
  Quotient.mk (coordinatePermutationSetoid d R maxDegree maxRange) c


noncomputable def exhaustiveCoordinatePermutationClassTable
    (d R maxDegree maxRange : ℕ) :
    Finset (CoordinatePermutationClass d R maxDegree maxRange) :=
  Finset.univ



theorem exhaustiveCoordinatePermutationClassTable_covers
    (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    coordinatePermutationClass c ∈
      exhaustiveCoordinatePermutationClassTable d R maxDegree maxRange := by
  classical
  simp [exhaustiveCoordinatePermutationClassTable]




def coordinateReflectionEquivalent {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) : Prop :=
  c.degree = c'.degree ∧ c.range = c'.range ∧
    ∃ ε : PolymerSupport.CoordinateReflection d,
      c'.toPolymerSupport = c.toPolymerSupport.reflectCoordinates ε

@[simp] theorem coordinateReflectionEquivalent_refl
    {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    coordinateReflectionEquivalent c c := by
  refine ⟨rfl, rfl, ⟨fun _ : Fin d => false, ?_⟩⟩
  simp

theorem coordinateReflectionEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : coordinateReflectionEquivalent c c') :
    coordinateReflectionEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, ε, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm, ⟨ε, ?_⟩⟩
  have hxor :
      (fun i : Fin d => Bool.xor (ε i) (ε i)) =
        (fun _ : Fin d => false) := by
    funext i
    cases ε i <;> rfl
  have hreflected :
      c'.toPolymerSupport.reflectCoordinates ε = c.toPolymerSupport := by
    rw [hsupport, PolymerSupport.reflectCoordinates_reflectCoordinates, hxor]
    simp
  exact hreflected.symm

theorem coordinateReflectionEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : coordinateReflectionEquivalent c₁ c₂)
    (h₂₃ : coordinateReflectionEquivalent c₂ c₃) :
    coordinateReflectionEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, ε, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, δ, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃,
    ⟨fun i => Bool.xor (ε i) (δ i), ?_⟩⟩
  calc
    c₃.toPolymerSupport = c₂.toPolymerSupport.reflectCoordinates δ := hsupport₂₃
    _ = (c₁.toPolymerSupport.reflectCoordinates ε).reflectCoordinates δ := by
      rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.reflectCoordinates
        (fun i => Bool.xor (ε i) (δ i)) := by
      rw [PolymerSupport.reflectCoordinates_reflectCoordinates]


def coordinateReflectionSetoid (d R maxDegree maxRange : ℕ) :
    Setoid (BoundedPolymerCase d R maxDegree maxRange) where
  r := coordinateReflectionEquivalent
  iseqv := by
    constructor
    · intro c
      exact coordinateReflectionEquivalent_refl c
    · intro c c' h
      exact coordinateReflectionEquivalent_symm h
    · intro c₁ c₂ c₃ h₁₂ h₂₃
      exact coordinateReflectionEquivalent_trans h₁₂ h₂₃


abbrev CoordinateReflectionClass (d R maxDegree maxRange : ℕ) : Type :=
  Quotient (coordinateReflectionSetoid d R maxDegree maxRange)



noncomputable instance coordinateReflectionClassFintype
    (d R maxDegree maxRange : ℕ) :
    Fintype (CoordinateReflectionClass d R maxDegree maxRange) := by
  classical
  unfold CoordinateReflectionClass
  infer_instance


def coordinateReflectionClass {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    CoordinateReflectionClass d R maxDegree maxRange :=
  Quotient.mk (coordinateReflectionSetoid d R maxDegree maxRange) c


noncomputable def exhaustiveCoordinateReflectionClassTable
    (d R maxDegree maxRange : ℕ) :
    Finset (CoordinateReflectionClass d R maxDegree maxRange) :=
  Finset.univ



theorem exhaustiveCoordinateReflectionClassTable_covers
    (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    coordinateReflectionClass c ∈
      exhaustiveCoordinateReflectionClassTable d R maxDegree maxRange := by
  classical
  simp [exhaustiveCoordinateReflectionClassTable]




def cubicEquivalent {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) : Prop :=
  c.degree = c'.degree ∧ c.range = c'.range ∧
    ∃ (v : Site d) (σ : Equiv.Perm (Fin d))
      (ε : PolymerSupport.CoordinateReflection d),
      c'.toPolymerSupport = c.toPolymerSupport.cubicTransform v σ ε

@[simp] theorem cubicEquivalent_refl {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    cubicEquivalent c c := by
  refine ⟨rfl, rfl, ⟨0, Equiv.refl (Fin d), fun _ : Fin d => false, ?_⟩⟩
  simp


theorem cubicEquivalent_support_card {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    c'.support.card = c.support.card := by
  rcases h with ⟨_, _, v, σ, ε, hsupport⟩
  calc
    c'.support.card = c'.toPolymerSupport.carrier.card :=
      (toPolymerSupport_card c').symm
    _ = (c.toPolymerSupport.cubicTransform v σ ε).carrier.card := by
      rw [hsupport]
    _ = c.toPolymerSupport.carrier.card := by
      rw [PolymerSupport.cubicTransform_card]
    _ = c.support.card := toPolymerSupport_card c



theorem cubicEquivalent_coordinateDiameterBound {d R maxDegree maxRange D : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c')
    (hdiam : c.toPolymerSupport.coordinateDiameterBound D) :
    c'.toPolymerSupport.coordinateDiameterBound D := by
  rcases h with ⟨_, _, v, σ, ε, hsupport⟩
  rw [hsupport]
  exact PolymerSupport.coordinateDiameterBound_cubicTransform σ ε hdiam

theorem cubicEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    cubicEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, v, σ, ε, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm,
    ⟨PolymerSupport.cubicInverseTranslation v σ ε, σ.symm, fun i => ε (σ i), ?_⟩⟩
  have hback :
      c'.toPolymerSupport.cubicTransform
        (PolymerSupport.cubicInverseTranslation v σ ε) σ.symm
        (fun i => ε (σ i)) = c.toPolymerSupport := by
    rw [hsupport]
    simp [PolymerSupport.cubicInverseTranslation]
  exact hback.symm

theorem cubicEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : cubicEquivalent c₁ c₂)
    (h₂₃ : cubicEquivalent c₂ c₃) :
    cubicEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, v, σ, ε, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, w, τ, δ, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃,
    ⟨PolymerSupport.reflectCoordinatesSite δ
        (PolymerSupport.permuteCoordinatesSite τ v) + w,
      σ.trans τ, fun i => Bool.xor (ε (τ.symm i)) (δ i), ?_⟩⟩
  calc
    c₃.toPolymerSupport =
        c₂.toPolymerSupport.cubicTransform w τ δ := hsupport₂₃
    _ = (c₁.toPolymerSupport.cubicTransform v σ ε).cubicTransform w τ δ := by
      rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.cubicTransform
        (PolymerSupport.reflectCoordinatesSite δ
          (PolymerSupport.permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
      rw [PolymerSupport.cubicTransform_cubicTransform]



theorem ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hbox' :
      (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicEquivalent
      (ofLocalCoordinate c hbox hdegree hrange)
      (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε)
        hbox' (by simpa using hdegree) (by simpa using hrange)) := by
  refine ⟨?_, ?_, v, σ, ε, ?_⟩
  · apply Fin.ext
    simp [ofLocalCoordinate, cubicTransformLocalCoordinate]
  · apply Fin.ext
    simp [ofLocalCoordinate, cubicTransformLocalCoordinate]
  · rw [toPolymerSupport_ofLocalCoordinate,
      toPolymerSupport_ofLocalCoordinate]
    rfl



theorem ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicEquivalent
      (ofLocalCoordinate c hbox hdegree hrange)
      (ofLocalCoordinate (permuteLocalCoordinate c σ)
        (permuteLocalCoordinate_containedInBox c σ hbox)
        (by simpa using hdegree) (by simpa using hrange)) := by
  refine ⟨?_, ?_, 0, σ, (fun _ : Fin d => false), ?_⟩
  · apply Fin.ext
    simp [ofLocalCoordinate, permuteLocalCoordinate]
  · apply Fin.ext
    simp [ofLocalCoordinate, permuteLocalCoordinate]
  · rw [toPolymerSupport_ofLocalCoordinate,
      toPolymerSupport_ofLocalCoordinate]
    ext x
    change x ∈ c.support.permuteCoordinates σ ↔
      x ∈ c.support.cubicTransform (0 : Site d) σ
        (fun _ : Fin d => false)
    constructor
    · intro hx
      rcases (PolymerSupport.mem_permuteCoordinates c.support σ x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_cubicTransform c.support
        (0 : Site d) σ (fun _ : Fin d => false) x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩
    · intro hx
      rcases (PolymerSupport.mem_cubicTransform c.support
          (0 : Site d) σ (fun _ : Fin d => false) x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_permuteCoordinates c.support σ x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩



theorem ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicEquivalent
      (ofLocalCoordinate c hbox hdegree hrange)
      (ofLocalCoordinate (reflectLocalCoordinate c ε)
        (reflectLocalCoordinate_containedInBox c ε hbox)
        (by simpa using hdegree) (by simpa using hrange)) := by
  refine ⟨?_, ?_, 0, Equiv.refl (Fin d), ε, ?_⟩
  · apply Fin.ext
    simp [ofLocalCoordinate, reflectLocalCoordinate]
  · apply Fin.ext
    simp [ofLocalCoordinate, reflectLocalCoordinate]
  · rw [toPolymerSupport_ofLocalCoordinate,
      toPolymerSupport_ofLocalCoordinate]
    ext x
    change x ∈ c.support.reflectCoordinates ε ↔
      x ∈ c.support.cubicTransform (0 : Site d) (Equiv.refl (Fin d)) ε
    constructor
    · intro hx
      rcases (PolymerSupport.mem_reflectCoordinates c.support ε x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_cubicTransform c.support
        (0 : Site d) (Equiv.refl (Fin d)) ε x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩
    · intro hx
      rcases (PolymerSupport.mem_cubicTransform c.support
          (0 : Site d) (Equiv.refl (Fin d)) ε x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_reflectCoordinates c.support ε x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩




def finiteCubicEquivalent {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) : Prop :=
  c.degree = c'.degree ∧ c.range = c'.range ∧
    ∃ (σ : Equiv.Perm (Fin d)) (ε : PolymerSupport.CoordinateReflection d),
      PolymerSupport.finiteTranslationEquivalent
        (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε)
        c'.toPolymerSupport

instance finiteCubicEquivalentDecidable {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) :
    Decidable (finiteCubicEquivalent c c') := by
  unfold finiteCubicEquivalent
  infer_instance

theorem finiteCubicEquivalent_iff {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) :
    finiteCubicEquivalent c c' ↔ cubicEquivalent c c' := by
  constructor
  · rintro ⟨hdegree, hrange, σ, ε, hfinite⟩
    rcases (PolymerSupport.finiteTranslationEquivalent_iff
      (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε)
      c'.toPolymerSupport).mp hfinite with ⟨v, htrans⟩
    refine ⟨hdegree, hrange, v, σ, ε, ?_⟩
    calc
      c'.toPolymerSupport =
          (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε).translate v :=
        htrans
      _ = c.toPolymerSupport.cubicTransform v σ ε := by
        rw [PolymerSupport.cubicTransform_zero_translate]
  · rintro ⟨hdegree, hrange, v, σ, ε, hsupport⟩
    refine ⟨hdegree, hrange, σ, ε, ?_⟩
    apply (PolymerSupport.finiteTranslationEquivalent_iff
      (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε)
      c'.toPolymerSupport).mpr
    refine ⟨v, ?_⟩
    rw [hsupport, PolymerSupport.cubicTransform_zero_translate]

instance instCubicEquivalentDecidableRel (d R maxDegree maxRange : ℕ) :
    DecidableRel (@cubicEquivalent d R maxDegree maxRange) := fun c c' =>
  decidable_of_iff (finiteCubicEquivalent c c')
    (finiteCubicEquivalent_iff c c')


def cubicSetoid (d R maxDegree maxRange : ℕ) :
    Setoid (BoundedPolymerCase d R maxDegree maxRange) where
  r := cubicEquivalent
  iseqv := by
    constructor
    · intro c
      exact cubicEquivalent_refl c
    · intro c c' h
      exact cubicEquivalent_symm h
    · intro c₁ c₂ c₃ h₁₂ h₂₃
      exact cubicEquivalent_trans h₁₂ h₂₃


abbrev CubicClass (d R maxDegree maxRange : ℕ) : Type :=
  Quotient (cubicSetoid d R maxDegree maxRange)



noncomputable instance cubicClassFintype (d R maxDegree maxRange : ℕ) :
    Fintype (CubicClass d R maxDegree maxRange) := by
  classical
  unfold CubicClass
  infer_instance





noncomputable instance cubicClassDecidableEq (d R maxDegree maxRange : ℕ) :
    DecidableEq (CubicClass d R maxDegree maxRange) :=
  Classical.decEq _


def cubicClass {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    CubicClass d R maxDegree maxRange :=
  Quotient.mk (cubicSetoid d R maxDegree maxRange) c



theorem cubicClass_ofLocalCoordinate_cubicTransformLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hbox' :
      (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicClass (ofLocalCoordinate c hbox hdegree hrange) =
      cubicClass
        (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε)
          hbox' (by simpa using hdegree) (by simpa using hrange)) :=
  Quotient.sound
    (ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent
      c v σ ε hbox hbox' hdegree hrange)



theorem cubicClass_ofLocalCoordinate_permuteLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicClass (ofLocalCoordinate c hbox hdegree hrange) =
      cubicClass
        (ofLocalCoordinate (permuteLocalCoordinate c σ)
          (permuteLocalCoordinate_containedInBox c σ hbox)
          (by simpa using hdegree) (by simpa using hrange)) :=
  Quotient.sound
    (ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent
      c σ hbox hdegree hrange)



theorem cubicClass_ofLocalCoordinate_reflectLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicClass (ofLocalCoordinate c hbox hdegree hrange) =
      cubicClass
        (ofLocalCoordinate (reflectLocalCoordinate c ε)
          (reflectLocalCoordinate_containedInBox c ε hbox)
          (by simpa using hdegree) (by simpa using hrange)) :=
  Quotient.sound
    (ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent
      c ε hbox hdegree hrange)




noncomputable def cubicRepresentative {d R maxDegree maxRange : ℕ}
    (q : CubicClass d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  Quotient.out q

@[simp] theorem cubicRepresentative_class {d R maxDegree maxRange : ℕ}
    (q : CubicClass d R maxDegree maxRange) :
    cubicClass (cubicRepresentative q) = q := by
  simp [cubicClass, cubicRepresentative, Quotient.out_eq q]



theorem cubicRepresentative_equivalent {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    cubicEquivalent (cubicRepresentative (cubicClass c)) c := by
  have hq :
      cubicClass (cubicRepresentative (cubicClass c)) = cubicClass c :=
    cubicRepresentative_class (cubicClass c)
  exact Quotient.exact hq



noncomputable def cubicOrbitFiber {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    Finset (BoundedPolymerCase d R maxDegree maxRange) :=
  Finset.univ.filter fun c' => cubicEquivalent c' c

@[simp] theorem mem_cubicOrbitFiber {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange} :
    c' ∈ cubicOrbitFiber c ↔ cubicEquivalent c' c := by
  simp [cubicOrbitFiber]


theorem cubicOrbitFiber_nonempty {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (cubicOrbitFiber c).Nonempty := by
  exact ⟨c, by simp [cubicOrbitFiber]⟩


theorem cubicOrbitFiber_eq_of_equivalent {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    cubicOrbitFiber c = cubicOrbitFiber c' := by
  ext x
  constructor
  · intro hx
    exact mem_cubicOrbitFiber.mpr
      (cubicEquivalent_trans (mem_cubicOrbitFiber.mp hx) h)
  · intro hx
    exact mem_cubicOrbitFiber.mpr
      (cubicEquivalent_trans (mem_cubicOrbitFiber.mp hx)
        (cubicEquivalent_symm h))





noncomputable def minimalCubicRepresentativeOfCase {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  (cubicOrbitFiber c).min' (cubicOrbitFiber_nonempty c)


theorem minimalCubicRepresentativeOfCase_eq_of_equivalent
    {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    minimalCubicRepresentativeOfCase c = minimalCubicRepresentativeOfCase c' := by
  simp [minimalCubicRepresentativeOfCase, cubicOrbitFiber_eq_of_equivalent h]



noncomputable def minimalCubicRepresentative {d R maxDegree maxRange : ℕ}
    (q : CubicClass d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  Quotient.lift minimalCubicRepresentativeOfCase
    (fun _ _ h => minimalCubicRepresentativeOfCase_eq_of_equivalent h) q

@[simp] theorem minimalCubicRepresentative_class {d R maxDegree maxRange : ℕ}
    (q : CubicClass d R maxDegree maxRange) :
    cubicClass (minimalCubicRepresentative q) = q := by
  refine Quotient.inductionOn q ?_
  intro c
  apply Quotient.sound
  exact mem_cubicOrbitFiber.mp
    (Finset.min'_mem (cubicOrbitFiber c) (cubicOrbitFiber_nonempty c))


noncomputable def exhaustiveCubicClassTable
    (d R maxDegree maxRange : ℕ) :
    Finset (CubicClass d R maxDegree maxRange) :=
  Finset.univ




theorem exhaustiveCubicClassTable_covers
    (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    cubicClass c ∈ exhaustiveCubicClassTable d R maxDegree maxRange := by
  classical
  simp [exhaustiveCubicClassTable]


noncomputable def exhaustiveTable (d R maxDegree maxRange : ℕ) :
    Finset (BoundedPolymerCase d R maxDegree maxRange) :=
  Finset.univ


theorem exhaustiveTable_covers (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c ∈ exhaustiveTable d R maxDegree maxRange := by
  classical
  simp [exhaustiveTable]



theorem exhaustiveTable_covers_localCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ofLocalCoordinate c hbox hdegree hrange ∈
      exhaustiveTable d R maxDegree maxRange := by
  exact exhaustiveTable_covers d R maxDegree maxRange
    (ofLocalCoordinate c hbox hdegree hrange)



theorem exhaustiveTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      bc ∈ exhaustiveTable d R maxDegree maxRange ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc, exhaustiveTable_covers d R maxDegree maxRange bc,
    hdeg, hrange', hsupport⟩


theorem exhaustiveTable_covers_boundedLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    classifyBoundedLocalCoordinate c ∈
      exhaustiveTable d R maxDegree maxRange := by
  exact exhaustiveTable_covers d R maxDegree maxRange
    (classifyBoundedLocalCoordinate c)



theorem caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hT : exhaustiveTable d R maxDegree maxRange ⊆ T.cases) :
    RatInterval.CaseTable.Covers T
      (@classifyBoundedLocalCoordinate d R maxDegree maxRange) := by
  intro c
  exact hT (exhaustiveTable_covers_boundedLocalCoordinate c)




theorem caseTable_covers_and_sound_boundedLocalCoordinate_of_caseValue
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hcover : exhaustiveTable d R maxDegree maxRange ⊆ T.cases)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hcase : ∀ k, k ∈ T.cases → (T.interval k).MemR (caseValue k)) :
    RatInterval.CaseTable.Covers T
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) ∧
      RatInterval.CaseTable.Sound T
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) value := by
  constructor
  · exact caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset
      T hcover
  · intro c
    rw [hvalue c]
    exact hcase (classifyBoundedLocalCoordinate c)
      ((caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset
        T hcover) c)




noncomputable def generatedIntervalTable {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange) where
  cases := exhaustiveTable d R maxDegree maxRange
  interval := intervalOf


theorem generatedIntervalTable_covers {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedIntervalTable intervalOf) id := by
  intro c
  exact exhaustiveTable_covers d R maxDegree maxRange c




theorem generatedIntervalTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      bc ∈ (generatedIntervalTable intervalOf).cases ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc, (generatedIntervalTable_covers intervalOf) bc,
    hdeg, hrange', hsupport⟩



theorem generatedIntervalTable_sound_of_caseValue {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c)) :
    RatInterval.CaseTable.Sound
      (generatedIntervalTable intervalOf) id caseValue := by
  intro c
  exact hcase c




theorem generatedIntervalTable_covers_and_sound_boundedLocalCoordinate_of_caseValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c)) :
    RatInterval.CaseTable.Covers
        (generatedIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) ∧
      RatInterval.CaseTable.Sound
        (generatedIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) value := by
  constructor
  · intro c
    exact exhaustiveTable_covers_boundedLocalCoordinate c
  · intro c
    rw [hvalue c]
    exact hcase (classifyBoundedLocalCoordinate c)


noncomputable def generatedStableKeyIntervalTable {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable (StableKey maxDegree maxRange) where
  cases := (exhaustiveTable d R maxDegree maxRange).image stableKey
  interval := intervalOf


theorem generatedStableKeyIntervalTable_covers_boundedCase
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
      (@stableKey d R maxDegree maxRange) := by
  intro c
  exact Finset.mem_image.mpr
    ⟨c, exhaustiveTable_covers d R maxDegree maxRange c, rfl⟩




theorem generatedStableKeyIntervalTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      stableKey bc ∈
          (generatedStableKeyIntervalTable
            (d := d) (R := R) intervalOf).cases ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc,
    (generatedStableKeyIntervalTable_covers_boundedCase intervalOf) bc,
    hdeg, hrange', hsupport⟩



theorem generatedStableKeyIntervalTable_sound_boundedCase_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hvalue : ∀ c, caseValue c = keyValue (stableKey c))
    (hkey : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := R) intervalOf).cases →
        (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Sound
      (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
      (@stableKey d R maxDegree maxRange) caseValue := by
  intro c
  rw [hvalue c]
  exact hkey (stableKey c)
    ((generatedStableKeyIntervalTable_covers_boundedCase
      (d := d) (R := R) intervalOf) c)



theorem generatedStableKeyTable_covers_and_sound_boundedLocal_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hvalue : ∀ c,
      value c = keyValue (stableKey (classifyBoundedLocalCoordinate c)))
    (hkey : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := R) intervalOf).cases →
        (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Covers
        (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) value := by
  constructor
  · intro c
    exact (generatedStableKeyIntervalTable_covers_boundedCase
      (d := d) (R := R) intervalOf) (classifyBoundedLocalCoordinate c)
  · intro c
    rw [hvalue c]
    exact hkey (stableKey (classifyBoundedLocalCoordinate c))
      ((generatedStableKeyIntervalTable_covers_boundedCase
        (d := d) (R := R) intervalOf) (classifyBoundedLocalCoordinate c))



def classifyBoundedLocalCoordinateCubicClass {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    CubicClass d R maxDegree maxRange :=
  cubicClass (classifyBoundedLocalCoordinate c)



noncomputable def generatedCubicIntervalTable {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable (CubicClass d R maxDegree maxRange) where
  cases := exhaustiveCubicClassTable d R maxDegree maxRange
  interval := intervalOf



theorem generatedCubicIntervalTable_covers_boundedCase
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedCubicIntervalTable intervalOf)
      (@cubicClass d R maxDegree maxRange) := by
  intro c
  exact exhaustiveCubicClassTable_covers d R maxDegree maxRange c




theorem generatedCubicIntervalTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      cubicClass bc ∈ (generatedCubicIntervalTable intervalOf).cases ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc, (generatedCubicIntervalTable_covers_boundedCase intervalOf) bc,
    hdeg, hrange', hsupport⟩



theorem generatedCubicIntervalTable_covers_boundedLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedCubicIntervalTable intervalOf)
      (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) := by
  intro c
  exact exhaustiveCubicClassTable_covers d R maxDegree maxRange
    (classifyBoundedLocalCoordinate c)




theorem generatedCubicIntervalTable_sound_boundedCase_of_classValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (classValue : CubicClass d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, caseValue c = classValue (cubicClass c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q)) :
    RatInterval.CaseTable.Sound
      (generatedCubicIntervalTable intervalOf)
      (@cubicClass d R maxDegree maxRange) caseValue := by
  intro c
  rw [hvalue c]
  exact hclass (cubicClass c)



theorem generatedCubicIntervalTable_covers_and_sound_boundedLocalCoordinate_of_classValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (classValue : CubicClass d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c,
      value c = classValue (classifyBoundedLocalCoordinateCubicClass c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q)) :
    RatInterval.CaseTable.Covers
        (generatedCubicIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) ∧
      RatInterval.CaseTable.Sound
        (generatedCubicIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) value := by
  constructor
  · exact generatedCubicIntervalTable_covers_boundedLocalCoordinate intervalOf
  · intro c
    rw [hvalue c]
    exact hclass (classifyBoundedLocalCoordinateCubicClass c)




def CubicRepresentativeTableCovers {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)) :
    Prop :=
  ∀ c : BoundedPolymerCase d R maxDegree maxRange,
    ∃ r, r ∈ T.cases ∧ cubicEquivalent r c




noncomputable def classifyByCubicRepresentative {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  Classical.choose (hcover c)


theorem classifyByCubicRepresentative_mem {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    classifyByCubicRepresentative T hcover c ∈ T.cases :=
  (Classical.choose_spec (hcover c)).1



theorem classifyByCubicRepresentative_equivalent {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    cubicEquivalent (classifyByCubicRepresentative T hcover c) c :=
  (Classical.choose_spec (hcover c)).2



theorem cubicRepresentativeTable_covers
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T) :
    RatInterval.CaseTable.Covers T
      (classifyByCubicRepresentative T hcover) := by
  intro c
  exact classifyByCubicRepresentative_mem T hcover c




theorem cubicRepresentativeTable_sound_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
    RatInterval.CaseTable.Sound T
      (classifyByCubicRepresentative T hcover) caseValue := by
  intro c
  have heq :
      caseValue c = caseValue (classifyByCubicRepresentative T hcover c) :=
    hinv (classifyByCubicRepresentative_equivalent T hcover c)
  rw [heq]
  exact hcase (classifyByCubicRepresentative T hcover c)
    (classifyByCubicRepresentative_mem T hcover c)


theorem cubicRepresentativeTable_covers_and_sound_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers T
        (classifyByCubicRepresentative T hcover) ∧
      RatInterval.CaseTable.Sound T
        (classifyByCubicRepresentative T hcover) caseValue := by
  exact ⟨cubicRepresentativeTable_covers T hcover,
    cubicRepresentativeTable_sound_of_cubicInvariant
      T hcover caseValue hinv hcase⟩



noncomputable def classifyBoundedLocalCoordinateByCubicRepresentative
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  classifyByCubicRepresentative T hcover (classifyBoundedLocalCoordinate c)



theorem cubicRepresentativeTable_covers_boundedLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T) :
    RatInterval.CaseTable.Covers T
      (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) := by
  intro c
  exact classifyByCubicRepresentative_mem T hcover
    (classifyBoundedLocalCoordinate c)




theorem cubicRepresentativeTable_covers_and_sound_boundedLocalCoordinate_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers T
        (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) ∧
      RatInterval.CaseTable.Sound T
        (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) value := by
  constructor
  · exact cubicRepresentativeTable_covers_boundedLocalCoordinate T hcover
  · intro c
    rw [hvalue c]
    have heq :
        caseValue (classifyBoundedLocalCoordinate c) =
          caseValue
            (classifyBoundedLocalCoordinateByCubicRepresentative T hcover c) :=
      hinv (classifyByCubicRepresentative_equivalent T hcover
        (classifyBoundedLocalCoordinate c))
    rw [heq]
    exact hcase (classifyBoundedLocalCoordinateByCubicRepresentative T hcover c)
      (classifyByCubicRepresentative_mem T hcover
        (classifyBoundedLocalCoordinate c))



noncomputable def generatedMinimalCubicRepresentativeTable
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange) where
  cases :=
    (exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicRepresentative
  interval := intervalOf



theorem generatedMinimalCubicRepresentativeTable_covers
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval) :
    CubicRepresentativeTableCovers
      (generatedMinimalCubicRepresentativeTable intervalOf) := by
  intro c
  refine ⟨minimalCubicRepresentative (cubicClass c), ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨cubicClass c,
        exhaustiveCubicClassTable_covers d R maxDegree maxRange c, rfl⟩
  · have hclass :
        cubicClass (minimalCubicRepresentative (cubicClass c)) =
          cubicClass c :=
      minimalCubicRepresentative_class (cubicClass c)
    exact Quotient.exact hclass





theorem generatedMinimalCubicRepresentativeTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc r : BoundedPolymerCase d R maxDegree maxRange),
      r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases ∧
        cubicEquivalent r bc ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  rcases generatedMinimalCubicRepresentativeTable_covers intervalOf bc with
    ⟨r, hrmem, hequiv⟩
  exact ⟨v, bc, r, hrmem, hequiv, hdeg, hrange', hsupport⟩



theorem generatedMinimalCubicRepresentativeTable_covers_and_sound_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r,
      r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases →
        (intervalOf r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf)) ∧
      RatInterval.CaseTable.Sound
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf))
        caseValue := by
  exact cubicRepresentativeTable_covers_and_sound_of_cubicInvariant
    (generatedMinimalCubicRepresentativeTable intervalOf)
    (generatedMinimalCubicRepresentativeTable_covers intervalOf)
    caseValue hinv hcase




theorem minimalRepTable_covers_and_sound_boundedLocal_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r,
      r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases →
        (intervalOf r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyBoundedLocalCoordinateByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf)) ∧
      RatInterval.CaseTable.Sound
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyBoundedLocalCoordinateByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf))
        value := by
  exact cubicRepresentativeTable_covers_and_sound_boundedLocalCoordinate_of_cubicInvariant
    (generatedMinimalCubicRepresentativeTable intervalOf)
    (generatedMinimalCubicRepresentativeTable_covers intervalOf)
    value caseValue hvalue hinv hcase


noncomputable def minimalCubicStableKey {d R maxDegree maxRange : ℕ}
    (q : CubicClass d R maxDegree maxRange) : StableKey maxDegree maxRange :=
  stableKey (minimalCubicRepresentative q)



noncomputable def classifyByMinimalCubicStableKey {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    StableKey maxDegree maxRange :=
  minimalCubicStableKey (cubicClass c)



theorem classifyByMinimalCubicStableKey_eq_of_equivalent
    {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    classifyByMinimalCubicStableKey c =
      classifyByMinimalCubicStableKey c' := by
  exact congrArg minimalCubicStableKey (Quotient.sound h)



theorem classifyByMinimalCubicStableKey_ofLocalCoordinate_cubicTransform
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hbox' :
      (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    classifyByMinimalCubicStableKey
        (ofLocalCoordinate c hbox hdegree hrange) =
      classifyByMinimalCubicStableKey
        (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε)
          hbox' (by simpa using hdegree) (by simpa using hrange)) := by
  exact classifyByMinimalCubicStableKey_eq_of_equivalent
    (ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent
      c v σ ε hbox hbox' hdegree hrange)



theorem classifyByMinimalCubicStableKey_ofLocalCoordinate_permute
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    classifyByMinimalCubicStableKey
        (ofLocalCoordinate c hbox hdegree hrange) =
      classifyByMinimalCubicStableKey
        (ofLocalCoordinate (permuteLocalCoordinate c σ)
          (permuteLocalCoordinate_containedInBox c σ hbox)
          (by simpa using hdegree) (by simpa using hrange)) := by
  exact classifyByMinimalCubicStableKey_eq_of_equivalent
    (ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent
      c σ hbox hdegree hrange)



theorem classifyByMinimalCubicStableKey_ofLocalCoordinate_reflect
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    classifyByMinimalCubicStableKey
        (ofLocalCoordinate c hbox hdegree hrange) =
      classifyByMinimalCubicStableKey
        (ofLocalCoordinate (reflectLocalCoordinate c ε)
          (reflectLocalCoordinate_containedInBox c ε hbox)
          (by simpa using hdegree) (by simpa using hrange)) := by
  exact classifyByMinimalCubicStableKey_eq_of_equivalent
    (ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent
      c ε hbox hdegree hrange)



noncomputable def generatedMinimalCubicStableKeyTable {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable (StableKey maxDegree maxRange) where
  cases :=
    (exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey
  interval := intervalOf


theorem generatedMinimalCubicStableKeyTable_covers_boundedCase
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf)
      (@classifyByMinimalCubicStableKey d R maxDegree maxRange) := by
  intro c
  exact Finset.mem_image.mpr
    ⟨cubicClass c,
      exhaustiveCubicClassTable_covers d R maxDegree maxRange c, rfl⟩




theorem generatedMinimalCubicStableKeyTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      classifyByMinimalCubicStableKey bc ∈
          (generatedMinimalCubicStableKeyTable
            (d := d) (R := R) intervalOf).cases ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc,
    (generatedMinimalCubicStableKeyTable_covers_boundedCase intervalOf) bc,
    hdeg, hrange', hsupport⟩



theorem generatedMinimalCubicStableKeyTable_sound_boundedCase_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hvalue : ∀ c, caseValue c =
      keyValue (classifyByMinimalCubicStableKey c))
    (hkey : ∀ k,
      k ∈ (generatedMinimalCubicStableKeyTable
          (d := d) (R := R) intervalOf).cases →
        (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Sound
      (generatedMinimalCubicStableKeyTable (d := d) (R := R) intervalOf)
      (@classifyByMinimalCubicStableKey d R maxDegree maxRange) caseValue := by
  intro c
  rw [hvalue c]
  exact hkey (classifyByMinimalCubicStableKey c)
    ((generatedMinimalCubicStableKeyTable_covers_boundedCase
      (d := d) (R := R) intervalOf) c)


theorem minimalCubicStableKeyTable_covers_and_sound_boundedLocal_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hvalue : ∀ c,
      value c =
        keyValue
          (classifyByMinimalCubicStableKey
            (classifyBoundedLocalCoordinate c)))
    (hkey : ∀ k,
      k ∈ (generatedMinimalCubicStableKeyTable
          (d := d) (R := R) intervalOf).cases →
        (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Covers
        (generatedMinimalCubicStableKeyTable
          (d := d) (R := R) intervalOf)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey
            (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (generatedMinimalCubicStableKeyTable
          (d := d) (R := R) intervalOf)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey
            (classifyBoundedLocalCoordinate c)) value := by
  constructor
  · intro c
    exact (generatedMinimalCubicStableKeyTable_covers_boundedCase
      (d := d) (R := R) intervalOf) (classifyBoundedLocalCoordinate c)
  · intro c
    rw [hvalue c]
    exact hkey
      (classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c))
      ((generatedMinimalCubicStableKeyTable_covers_boundedCase
        (d := d) (R := R) intervalOf) (classifyBoundedLocalCoordinate c))




noncomputable def coarseIntervalTable (d R maxDegree maxRange : ℕ) :
    RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange) where
  cases := exhaustiveTable d R maxDegree maxRange
  interval := fun _ =>
    { lower := -1
      upper := 1
      lower_le_upper := by norm_num }


theorem coarseIntervalTable_covers (d R maxDegree maxRange : ℕ) :
    RatInterval.CaseTable.Covers
      (coarseIntervalTable d R maxDegree maxRange) id := by
  intro c
  exact exhaustiveTable_covers d R maxDegree maxRange c


theorem coarseIntervalTable_sound_of_abs_le_one {d R maxDegree maxRange : ℕ}
    (value : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, |value c| ≤ 1) :
    RatInterval.CaseTable.Sound
      (coarseIntervalTable d R maxDegree maxRange) id value := by
  intro c
  have h := hvalue c
  rw [abs_le] at h
  simpa [coarseIntervalTable, RatInterval.MemR] using h

end BoundedPolymerCase

end

end Exact3D
end StatMech
