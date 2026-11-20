/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexLiteralHWDepth
import Code.Universality.HexLiteralHWAugment

namespace StatMech.Universality

open HexWalk

noncomputable section



theorem hlhda_returnPos_injective : Function.Injective hexAWReturnPos := by
  intro c d h
  apply hexAWPos_injective
  rw [hexAWPos_eq_returnPos_mul, hexAWPos_eq_returnPos_mul, h]

theorem hlhda_coordRuns_pos_eq (p d : HexReturnCoord) (ts : List ℤ) :
    (hlhr_coordRun p d ts).pos = (hexEndpointCoordRun p d ts).pos := by
  induction ts generalizing p d with
  | nil => rfl
  | cons t ts ih =>
      simpa [hlhr_coordRun, hexEndpointCoordRun] using
        ih (p.add (d.turn t)) (d.turn t)

theorem hlhda_prefixCoord_returnPos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) :
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (ts.take k)).pos =
      hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k) := by
  rw [hlhda_coordRuns_pos_eq]
  exact hexEndpointCoordRun_pos_eq_aw (ts.take k)
    (hlhc_prefixCoord ts hleg.1 k)
    (by
      intro t ht
      exact hleg.1 t (List.mem_of_mem_take ht))
    (hlhc_prefixCoord_vertex ts hleg.1 k)

@[simp] theorem hlhda_prefixCoord_zero (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhc_prefixCoord ts hleg.1 0 = hexAWOriginCoord := by
  apply hlhda_returnPos_injective
  rw [← hlhda_prefixCoord_returnPos ts hleg 0]
  rfl

@[simp] theorem hlhda_depth_zero (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhd_depth ts hleg 0 = 0 := by
  unfold hlhd_depth
  rw [hlhda_prefixCoord_zero ts hleg]
  rfl

theorem hlhda_depth_one (t : ℤ) (us : List ℤ)
    (hleg : (ofTurns hexAWStart 1 (t :: us)).IsLegalSAW) :
    hlhd_depth (t :: us) hleg 1 = 1 := by
  have ht := hleg.1 t (by simp)
  rcases ht with rfl | rfl
  · have hc : hlhc_prefixCoord ((1 : ℤ) :: us) hleg.1 1 =
        ⟨0, -1, .white⟩ := by
      apply hlhda_returnPos_injective
      rw [← hlhda_prefixCoord_returnPos ((1 : ℤ) :: us) hleg 1]
      simp [hlhr_coordRun, HexReturnCoord.zero, HexReturnCoord.base,
        HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.add,
        hexAWReturnPos]
    simp [hlhd_depth, hc, hexAWDepth, hexAWLong]
  · have hc : hlhc_prefixCoord ((-1 : ℤ) :: us) hleg.1 1 =
        ⟨-1, 0, .white⟩ := by
      apply hlhda_returnPos_injective
      rw [← hlhda_prefixCoord_returnPos ((-1 : ℤ) :: us) hleg 1]
      simp [hlhr_coordRun, HexReturnCoord.zero, HexReturnCoord.base,
        HexReturnCoord.turn, HexReturnCoord.right, HexReturnCoord.add,
        hexAWReturnPos]
    simp [hlhd_depth, hc, hexAWDepth, hexAWLong]

theorem hlhda_returnScore_exact (c : HexAWCoord) :
    2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y =
      match c.color with
      | .black => 3 * hexAWDepth c
      | .white => 3 * hexAWDepth c - 2 := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp [hexAWReturnPos, hexAWDepth, hexAWLong] <;> omega

theorem hlhda_depth_pos_of_returnScore_pos (c : HexAWCoord)
    (hscore : 0 < 2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y) :
    0 < hexAWDepth c := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp [hexAWReturnPos, hexAWDepth, hexAWLong] at hscore ⊢ <;> omega



theorem hlhda_exists_firstMax (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    ∃ cp, cp ≤ ts.length ∧
      (∀ k ≤ ts.length, hlhd_depth ts hleg k ≤ hlhd_depth ts hleg cp) ∧
      ∀ k, k < cp → hlhd_depth ts hleg k < hlhd_depth ts hleg cp := by
  classical
  set n := ts.length with hn
  set f := fun k => hlhd_depth ts hleg k with hf
  obtain ⟨c, hc, hmax⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) f ⟨0, by simp⟩
  rw [Finset.mem_range] at hc
  set M := f c with hM
  have hmaxval : ∀ k ≤ n, f k ≤ M := fun k hk =>
    hmax k (Finset.mem_range.mpr (by omega))
  have hex : ∃ k, k ≤ n ∧ f k = M := ⟨c, by omega, rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_⟩
  · intro k hk
    show f k ≤ f (Nat.find hex)
    rw [(Nat.find_spec hex).2]
    exact hmaxval k hk
  · intro k hk
    show f k < f (Nat.find hex)
    have hnot : ¬ (k ≤ n ∧ f k = M) :=
      (Nat.lt_find_iff hex k).mp hk k le_rfl
    have hkn : k ≤ n := by
      have := Nat.find_spec hex
      omega
    have hle := hmaxval k hkn
    rw [(Nat.find_spec hex).2]
    exact lt_of_le_of_ne hle (fun heq => hnot ⟨hkn, heq⟩)

noncomputable def hlhda_cutPos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : ℕ :=
  (hlhda_exists_firstMax ts hleg).choose

theorem hlhda_cutPos_le (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_cutPos ts hleg ≤ ts.length :=
  (hlhda_exists_firstMax ts hleg).choose_spec.1

theorem hlhda_cutPos_max (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k ≤ ts.length) :
    hlhd_depth ts hleg k ≤ hlhd_depth ts hleg (hlhda_cutPos ts hleg) :=
  (hlhda_exists_firstMax ts hleg).choose_spec.2.1 k hk

theorem hlhda_cutPos_first (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k < hlhda_cutPos ts hleg) :
    hlhd_depth ts hleg k < hlhd_depth ts hleg (hlhda_cutPos ts hleg) :=
  (hlhda_exists_firstMax ts hleg).choose_spec.2.2 k hk

theorem hlhda_cutPos_pos {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ []) :
    0 < hlhda_cutPos ts hleg := by
  obtain ⟨t, us, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hmax := hlhda_cutPos_max (t :: us) hleg 1 (by simp)
  rw [hlhda_depth_one t us hleg] at hmax
  by_contra hpos
  have hzero : hlhda_cutPos (t :: us) hleg = 0 := Nat.eq_zero_of_not_pos hpos
  rw [hzero, hlhda_depth_zero] at hmax
  omega



def hlhda_score (p : HexReturnCoord) : ℤ := 2 * p.x - p.y

def hlhda_spacerWhite : HexReturnCoord := ⟨0, -1⟩

def hlhda_spacerRoot : HexReturnCoord := ⟨1, -1⟩

def hlhda_flatNeighbor : HexReturnCoord := ⟨-1, 0⟩

theorem hlhda_firstDir_mem_edgeVertices (d : HexReturnCoord) (ts : List ℤ) :
    d ∈ hlha_edgeVertices HexReturnCoord.zero d ts := by
  cases ts with
  | nil => simp [hlha_edgeVertices, hlha_zero_add]
  | cons t ts =>
      simp only [hlha_edgeVertices, List.mem_cons]
      right
      simpa [hlha_zero_add] using
        hlha_edgeVertices_start_mem d (d.turn t) ts

theorem hlhda_halfSpace_congr {xs ys : List ℤ} (hxy : xs = ys)
    {hx : (ofTurns hexAWStart 1 xs).IsLegalSAW}
    {hy : (ofTurns hexAWStart 1 ys).IsLegalSAW}
    (hhalf : HLHDLiteralHalfSpace xs hx) :
    HLHDLiteralHalfSpace ys hy := by
  subst ys
  have hp : hx = hy := Subsingleton.elim _ _
  subst hy
  exact hhalf

def HLHDAInwardDir (d : HexReturnCoord) : Prop :=
  d = HexReturnCoord.base.turn 1 ∨
    d = HexReturnCoord.base.turn (-1)

def hlhda_entryTurn (d : HexReturnCoord) : ℤ :=
  if d = HexReturnCoord.base.turn 1 then 1 else -1

theorem hlhda_entryTurn_legal (d : HexReturnCoord) :
    hlhda_entryTurn d = 1 ∨ hlhda_entryTurn d = -1 := by
  unfold hlhda_entryTurn
  split <;> simp

theorem hlhda_entryTurn_dir {d : HexReturnCoord} (hd : HLHDAInwardDir d) :
    HexReturnCoord.base.turn (hlhda_entryTurn d) = d := by
  rcases hd with hd | hd
  · rw [hd]
    simp [hlhda_entryTurn]
  · rw [hd]
    simp [hlhda_entryTurn, HexReturnCoord.turn, HexReturnCoord.base,
      HexReturnCoord.left, HexReturnCoord.right]



def hlhda_augmentSide (d : HexReturnCoord) (internal : List ℤ) : List ℤ :=
  [-1, 1, hlhda_entryTurn d] ++ internal



def hlhda_emptySide : List ℤ := [-1, 1]

@[simp] theorem hlhda_augmentSide_length (d : HexReturnCoord)
    (internal : List ℤ) :
    (hlhda_augmentSide d internal).length = internal.length + 3 := by
  simp [hlhda_augmentSide]

@[simp] theorem hlhda_emptySide_length : hlhda_emptySide.length = 2 := rfl

theorem hlhda_augmentSide_legal (d : HexReturnCoord) (internal : List ℤ)
    (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1) :
    (ofTurns hexAWStart 1 (hlhda_augmentSide d internal)).LegalTurns := by
  intro t ht
  change t ∈ (-1 : ℤ) :: 1 :: hlhda_entryTurn d :: internal at ht
  simp only [List.mem_cons] at ht
  rcases ht with rfl | rfl | rfl | ht
  · simp
  · simp
  · exact hlhda_entryTurn_legal d
  · exact hlegal t ht

theorem hlhda_emptySide_legal :
    (ofTurns hexAWStart 1 hlhda_emptySide).LegalTurns := by
  intro t ht
  simp [hlhda_emptySide] at ht
  rcases ht with rfl | rfl <;> simp

theorem hlhda_coordVertices_augmentSide (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d) :
    hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (hlhda_augmentSide d internal) =
      HexReturnCoord.zero :: hlhda_spacerWhite ::
        (hlha_edgeVertices HexReturnCoord.zero d internal).map
          hlhda_spacerRoot.add := by
  rw [show hlhda_augmentSide d internal =
      (-1 : ℤ) :: 1 :: hlhda_entryTurn d :: internal by
    simp [hlhda_augmentSide]]
  simp only [hlha_coordVertices]
  change HexReturnCoord.zero :: hlhda_spacerWhite ::
      hlha_coordVertices hlhda_spacerRoot HexReturnCoord.base
          (hlhda_entryTurn d :: internal) = _
  rw [hlha_coordVertices_cons_eq_edge, hlhda_entryTurn_dir hd]
  have htrans := hlha_edgeVertices_translate hlhda_spacerRoot
    HexReturnCoord.zero d internal
  simpa [hlhda_spacerRoot] using htrans

theorem hlhda_coordVertices_emptySide :
    hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        hlhda_emptySide =
      [HexReturnCoord.zero, hlhda_spacerWhite, hlhda_spacerRoot] := by
  simp [hlhda_emptySide, hlha_coordVertices, hlhda_spacerWhite,
    hlhda_spacerRoot, HexReturnCoord.zero, HexReturnCoord.base,
    HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.right,
    HexReturnCoord.add]

@[simp] theorem hlhda_score_zero :
    hlhda_score HexReturnCoord.zero = 0 := rfl

@[simp] theorem hlhda_score_spacerWhite :
    hlhda_score hlhda_spacerWhite = 1 := rfl

@[simp] theorem hlhda_score_spacerRoot :
    hlhda_score hlhda_spacerRoot = 3 := rfl

theorem hlhda_score_add (p q : HexReturnCoord) :
    hlhda_score (p.add q) = hlhda_score p + hlhda_score q := by
  cases p
  cases q
  simp [hlhda_score, HexReturnCoord.add]
  ring

theorem hlhda_spacerRoot_add_ne_zero (p : HexReturnCoord)
    (hp : -2 ≤ hlhda_score p) :
    hlhda_spacerRoot.add p ≠ HexReturnCoord.zero := by
  intro heq
  have hs := congrArg hlhda_score heq
  rw [hlhda_score_add] at hs
  simp at hs
  omega

theorem hlhda_spacerRoot_add_eq_white_iff (p : HexReturnCoord) :
    hlhda_spacerRoot.add p = hlhda_spacerWhite ↔
      p = hlhda_flatNeighbor := by
  rcases p with ⟨x, y⟩
  simp [hlhda_spacerRoot, hlhda_spacerWhite, hlhda_flatNeighbor,
    HexReturnCoord.add, HexReturnCoord.mk.injEq] <;> omega

theorem hlhda_coordVertices_augmentSide_nodup (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    (hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d internal) :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
      (hlhda_augmentSide d internal)).Nodup := by
  rw [hlhda_coordVertices_augmentSide d internal hd]
  simp only [List.nodup_cons]
  constructor
  · simp only [List.mem_cons, List.mem_map, not_or]
    constructor
    · decide
    · rintro ⟨p, hp, heq⟩
      exact hlhda_spacerRoot_add_ne_zero p (hscore p hp) heq
  · constructor
    · simp only [List.mem_map]
      rintro ⟨p, hp, heq⟩
      have hpflat := (hlhda_spacerRoot_add_eq_white_iff p).mp heq
      exact hflat (hpflat ▸ hp)
    · exact hnodup.map (hlha_add_left_injective hlhda_spacerRoot)

theorem hlhda_coordVertices_emptySide_nodup :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
      hlhda_emptySide).Nodup := by
  rw [hlhda_coordVertices_emptySide]
  decide

theorem hlhda_augmentSide_isLegalSAW (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    (hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d internal) :
    (ofTurns hexAWStart 1 (hlhda_augmentSide d internal)).IsLegalSAW := by
  have hturns := hlhda_augmentSide_legal d internal hlegal
  refine ⟨hturns, ?_⟩
  have hstdTurns : (ofTurns 0 0 (hlhda_augmentSide d internal)).LegalTurns :=
    hturns
  have hstdSaw : (ofTurns 0 0 (hlhda_augmentSide d internal)).IsSAW := by
    rw [hlha_standard_isSAW_iff _ hstdTurns]
    exact hlhda_coordVertices_augmentSide_nodup d internal hd hnodup
      hscore hflat
  exact (hhe_isSAW_rebase 0 hexAWStart 0 1
    (hlhda_augmentSide d internal)).mpr hstdSaw

theorem hlhda_emptySide_isLegalSAW :
    (ofTurns hexAWStart 1 hlhda_emptySide).IsLegalSAW := by
  refine ⟨hlhda_emptySide_legal, ?_⟩
  have hstdTurns : (ofTurns 0 0 hlhda_emptySide).LegalTurns :=
    hlhda_emptySide_legal
  have hstdSaw : (ofTurns 0 0 hlhda_emptySide).IsSAW := by
    rw [hlha_standard_isSAW_iff _ hstdTurns]
    exact hlhda_coordVertices_emptySide_nodup
  exact (hhe_isSAW_rebase 0 hexAWStart 0 1 hlhda_emptySide).mpr hstdSaw

theorem hlhda_augmentSide_runnerScore_pos (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    {k : ℕ} (hk : 0 < k)
    (hkle : k ≤ (hlhda_augmentSide d internal).length) :
    0 < hlhda_score
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        ((hlhda_augmentSide d internal).take k)).pos := by
  have hmem := hlha_coordRun_take_mem_tail HexReturnCoord.zero
    HexReturnCoord.base (hlhda_augmentSide d internal) hk hkle
  rw [hlhda_coordVertices_augmentSide d internal hd] at hmem
  simp only [List.tail_cons, List.mem_cons, List.mem_map] at hmem
  rcases hmem with heq | ⟨p, hp, heq⟩
  · rw [heq]
    simp
  · rw [← heq, hlhda_score_add]
    simp
    have hpScore := hscore p hp
    omega

theorem hlhda_emptySide_runnerScore_pos {k : ℕ} (hk : 0 < k)
    (hkle : k ≤ hlhda_emptySide.length) :
    0 < hlhda_score
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (hlhda_emptySide.take k)).pos := by
  have hmem := hlha_coordRun_take_mem_tail HexReturnCoord.zero
    HexReturnCoord.base hlhda_emptySide hk hkle
  rw [hlhda_coordVertices_emptySide] at hmem
  simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with heq | heq <;> rw [heq] <;> simp

theorem hlhda_augmentSide_halfSpace (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    (hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d internal) :
    HLHDLiteralHalfSpace (hlhda_augmentSide d internal)
      (hlhda_augmentSide_isLegalSAW d internal hd hlegal hnodup hscore hflat) := by
  let hleg := hlhda_augmentSide_isLegalSAW d internal hd hlegal hnodup
    hscore hflat
  intro k hk hkle
  have hs := hlhda_augmentSide_runnerScore_pos d internal hd hscore hk hkle
  have hr := hlhda_prefixCoord_returnPos
    (hlhda_augmentSide d internal) hleg k
  rw [hr] at hs
  have hdepth := hlhda_depth_pos_of_returnScore_pos _ hs
  change (hlhd_depth (hlhda_augmentSide d internal) hleg 0 : ℝ) <
    hlhd_depth (hlhda_augmentSide d internal) hleg k
  rw [hlhda_depth_zero]
  exact_mod_cast hdepth

theorem hlhda_emptySide_halfSpace :
    HLHDLiteralHalfSpace hlhda_emptySide hlhda_emptySide_isLegalSAW := by
  intro k hk hkle
  have hs := hlhda_emptySide_runnerScore_pos hk hkle
  have hr := hlhda_prefixCoord_returnPos hlhda_emptySide
    hlhda_emptySide_isLegalSAW k
  rw [hr] at hs
  have hdepth := hlhda_depth_pos_of_returnScore_pos _ hs
  change (hlhd_depth hlhda_emptySide hlhda_emptySide_isLegalSAW 0 : ℝ) <
    hlhd_depth hlhda_emptySide hlhda_emptySide_isLegalSAW k
  rw [hlhda_depth_zero]
  exact_mod_cast hdepth



noncomputable def hlhda_cutState (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : HLHRCoordRun :=
  hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
    (ts.take (hlhda_cutPos ts hleg))

theorem hlhda_neighbor_color_black {c d : HexAWCoord} {e : Fin 3}
    (hc : c.color = .black) (h : hexAWNeighbor c e = d) :
    d.color = .white := by
  subst d
  rcases c with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;> rfl

theorem hlhda_neighbor_color_white {c d : HexAWCoord} {e : Fin 3}
    (hc : c.color = .white) (h : hexAWNeighbor c e = d) :
    d.color = .black := by
  subst d
  rcases c with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;> rfl

theorem hlhda_cut_local {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ []) :
    let cp := hlhda_cutPos ts hleg
    (hlhc_prefixCoord ts hleg.1 (cp - 1)).color = .black ∧
      (hlhc_prefixCoord ts hleg.1 cp).color = .white ∧
      hlhd_depth ts hleg cp = hlhd_depth ts hleg (cp - 1) + 1 := by
  let cp := hlhda_cutPos ts hleg
  have hcpPos : 0 < cp := hlhda_cutPos_pos hleg hne
  have hcpLe : cp ≤ ts.length := hlhda_cutPos_le ts hleg
  have hklt : cp - 1 < ts.length := by omega
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg (cp - 1) hklt
  have hsucc : cp - 1 + 1 = cp := by omega
  have hstrict : hlhd_depth ts hleg (cp - 1) < hlhd_depth ts hleg cp :=
    hlhda_cutPos_first ts hleg (cp - 1) (by omega)
  have hcases := hlhd_neighbor_depth_cases
    (hlhc_prefixCoord ts hleg.1 (cp - 1)) e
  rw [he, hsucc] at hcases
  rcases hcases with hinc | hdec | hflat
  · exact ⟨hinc.2.1,
      hlhda_neighbor_color_black hinc.2.1 (he.trans (by rw [hsucc])),
      hinc.1⟩
  · unfold hlhd_depth at hstrict
    rw [hdec.1] at hstrict
    omega
  · unfold hlhd_depth at hstrict
    rw [hflat.1] at hstrict
    omega

theorem hlhda_coordRun_lastStep (p d : HexReturnCoord) (ts : List ℤ)
    {k : ℕ} (hk : 0 < k) (hkle : k ≤ ts.length) :
    (hlhr_coordRun p d (ts.take k)).pos =
      ((hlhr_coordRun p d (ts.take (k - 1))).pos.add
        (hlhr_coordRun p d (ts.take k)).dir) := by
  induction ts generalizing p d k with
  | nil => simp at hkle; omega
  | cons t ts ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero => simp [hlhr_coordRun]
          | succ k =>
              simp only [List.take_succ_cons, hlhr_coordRun, Nat.succ_sub_one]
              exact ih (p.add (d.turn t)) (d.turn t) (k := k + 1)
                (by omega) (by simpa using Nat.le_of_succ_le_succ hkle)

theorem hlhda_score_neg (p : HexReturnCoord) :
    hlhda_score (hlha_negCoord p) = -hlhda_score p := by
  cases p
  simp [hlhda_score, hlha_negCoord]
  ring

theorem hlhda_inward_of_unit_score_one (d : HexReturnCoord)
    (hu : d.IsUnit) (hs : hlhda_score d = 1) : HLHDAInwardDir d := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HLHDAInwardDir, HexReturnCoord.base, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right, hlhda_score] at hs ⊢

theorem hlhda_cutState_inward {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ []) :
    HLHDAInwardDir (hlhda_cutState ts hleg).dir := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let rp := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
    (ts.take (cp - 1))
  have hcpPos : 0 < cp := hlhda_cutPos_pos hleg hne
  have hcpLe : cp ≤ ts.length := hlhda_cutPos_le ts hleg
  have hstep := hlhda_coordRun_lastStep HexReturnCoord.zero
    HexReturnCoord.base ts hcpPos hcpLe
  change r.pos = rp.pos.add r.dir at hstep
  have hrPos : r.pos =
      hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp) := by
    exact hlhda_prefixCoord_returnPos ts hleg cp
  have hpPos : rp.pos =
      hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (cp - 1)) := by
    exact hlhda_prefixCoord_returnPos ts hleg (cp - 1)
  have hlocal := hlhda_cut_local hleg hne
  change
    (hlhc_prefixCoord ts hleg.1 (cp - 1)).color = .black ∧
      (hlhc_prefixCoord ts hleg.1 cp).color = .white ∧
      hlhd_depth ts hleg cp = hlhd_depth ts hleg (cp - 1) + 1 at hlocal
  have hscoreCut := hlhda_returnScore_exact
    (hlhc_prefixCoord ts hleg.1 cp)
  have hscorePrev := hlhda_returnScore_exact
    (hlhc_prefixCoord ts hleg.1 (cp - 1))
  rw [hlocal.2.1] at hscoreCut
  rw [hlocal.1] at hscorePrev
  change hlhda_score (hexAWReturnPos
      (hlhc_prefixCoord ts hleg.1 cp)) =
        3 * hlhd_depth ts hleg cp - 2 at hscoreCut
  change hlhda_score (hexAWReturnPos
      (hlhc_prefixCoord ts hleg.1 (cp - 1))) =
        3 * hlhd_depth ts hleg (cp - 1) at hscorePrev
  have hs : hlhda_score r.dir = 1 := by
    have hadd := congrArg hlhda_score hstep
    rw [hlhda_score_add, hrPos, hpPos] at hadd
    rw [hscoreCut, hscorePrev] at hadd
    omega
  have hu : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base (ts.take cp) HexReturnCoord.base_isUnit
    intro t ht
    exact hleg.1 t (List.mem_of_mem_take ht)
  exact hlhda_inward_of_unit_score_one r.dir hu hs

theorem hlhda_returnPos_normalize_down (source c : HexAWCoord)
    (hs : source.color = .white) :
    hexAWReturnPos (hlhd_normalizeCoord false source c) =
      (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c)) := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases sc
  · simp at hs
  · cases color <;>
      simp [hlhd_normalizeCoord, hlhd_swapColor, hexAWReturnPos,
        HexReturnCoord.add, hlha_negCoord] <;> congr <;> omega

theorem hlhda_normalized_score_lower (source c : HexAWCoord)
    (hs : source.color = .white)
    (hdepth : hexAWDepth c ≤ hexAWDepth source) :
    -2 ≤ hlhda_score
      ((hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c))) := by
  rw [← hlhda_returnPos_normalize_down source c hs]
  have hd := hlhd_normalizeCoord_depth false source c
  simp only [Bool.false_eq_true, ↓reduceIte] at hd
  have hsExact := hlhda_returnScore_exact
    (hlhd_normalizeCoord false source c)
  unfold hlhda_score
  rw [hsExact, hd]
  split <;> omega

theorem hlhda_normalized_eq_flat_iff (source c : HexAWCoord)
    (hs : source.color = .white) :
    (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c)) =
        hlhda_flatNeighbor ↔
      c = hexAWNeighbor source 0 := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases sc <;> cases color <;>
    simp_all [hexAWReturnPos, HexReturnCoord.add, hlha_negCoord,
      hlhda_flatNeighbor, hexAWNeighbor, HexReturnCoord.mk.injEq] <;> omega

@[simp] theorem hlhda_depth_neighbor_zero (c : HexAWCoord) :
    hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> simp [hexAWNeighbor, hexAWDepth, hexAWLong]

theorem hlhda_add_neg_add (p q : HexReturnCoord) :
    p.add (hlha_negCoord (p.add q)) = hlha_negCoord q := by
  cases p
  cases q
  simp [HexReturnCoord.add, hlha_negCoord]

theorem hlhda_prefix_normalized_point {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hpre : ts.take (hlhda_cutPos ts hleg) = t :: us)
    {q : HexReturnCoord}
    (hq : q ∈ hlha_edgeVertices HexReturnCoord.zero
      (hlhda_cutState ts hleg).dir (loopReverse us)) :
    ∃ k, k ≤ hlhda_cutPos ts hleg ∧
      q = (hexAWReturnPos
          (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add
        (hlha_negCoord (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k))) := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := HexReturnCoord.base.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_take
    rw [hpre]
    simp
  have ht := hleg.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hutake : u ∈ ts.take (hlhda_cutPos ts hleg) := by
      rw [hpre]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_take hutake)
  have hrevLegal : ∀ u ∈ loopReverse us, u = 1 ∨ u = -1 :=
    loopReverse_legal us hus
  have hrstate :
      hlhr_coordRun (HexReturnCoord.zero.add d0) d0 us = r := by
    dsimp [r, hlhda_cutState, d0]
    rw [hpre]
    simp only [hlhr_coordRun]
  have hrev := hlha_edgeVertices_loopReverse HexReturnCoord.zero d0 us hus
  rw [hrstate] at hrev
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us) hrevLegal
  simp only [hlha_negCoord_zero, hlha_negCoord_negCoord] at hneg
  rw [hneg, List.mem_map] at hq
  obtain ⟨p, hp, hqp⟩ := hq
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us)
  simp only [hlha_add_zero] at htrans
  have habs : r.pos.add p ∈
      hlha_edgeVertices r.pos (hlha_negCoord r.dir) (loopReverse us) := by
    rw [htrans, List.mem_map]
    exact ⟨p, hp, rfl⟩
  rw [hrev.1, List.mem_reverse] at habs
  have hforward : hlha_edgeVertices HexReturnCoord.zero d0 us =
      hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (ts.take cp) := by
    rw [hpre, hlha_coordVertices_cons_eq_edge]
  rw [hforward] at habs
  obtain ⟨k, hk, hkpos⟩ := hlha_mem_coordVertices
    HexReturnCoord.zero HexReturnCoord.base (ts.take cp) habs
  have hpreLen : (ts.take cp).length = cp := by
    rw [List.length_take_of_le (hlhda_cutPos_le ts hleg)]
  rw [hpreLen] at hk
  have htake : (ts.take cp).take k = ts.take k := by
    rw [List.take_take, Nat.min_eq_left hk]
  rw [htake] at hkpos
  have hkReturn := hlhda_prefixCoord_returnPos ts hleg k
  have hcpReturn := hlhda_prefixCoord_returnPos ts hleg cp
  refine ⟨k, hk, ?_⟩
  rw [← hkReturn, ← hcpReturn, ← hqp, ← hkpos]
  change hlha_negCoord p = r.pos.add (hlha_negCoord (r.pos.add p))
  exact (hlhda_add_neg_add r.pos p).symm

theorem hlhda_prefix_side_hypotheses {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ [])
    {t : ℤ} {us : List ℤ}
    (hpre : ts.take (hlhda_cutPos ts hleg) = t :: us) :
    let d := (hlhda_cutState ts hleg).dir
    HLHDAInwardDir d ∧
      (∀ u ∈ loopReverse us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup ∧
      (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d (loopReverse us),
        -2 ≤ hlhda_score q) ∧
      hlhda_flatNeighbor ∉
        hlha_edgeVertices HexReturnCoord.zero d (loopReverse us) := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := HexReturnCoord.base.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_take
    rw [hpre]
    simp
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hutake : u ∈ ts.take (hlhda_cutPos ts hleg) := by
      rw [hpre]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_take hutake)
  have hrevLegal : ∀ u ∈ loopReverse us, u = 1 ∨ u = -1 :=
    loopReverse_legal us hus
  have hrstate :
      hlhr_coordRun (HexReturnCoord.zero.add d0) d0 us = r := by
    dsimp [r, hlhda_cutState, d0]
    rw [hpre]
    simp only [hlhr_coordRun]
  have hrev := hlha_edgeVertices_loopReverse HexReturnCoord.zero d0 us hus
  rw [hrstate] at hrev
  have hforward : hlha_edgeVertices HexReturnCoord.zero d0 us =
      hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (ts.take cp) := by
    rw [hpre, hlha_coordVertices_cons_eq_edge]
  have hfullNodup := hlha_source_coord_nodup hexAWStart 1 ts hleg
  have hforwardNodup :
      (hlha_edgeVertices HexReturnCoord.zero d0 us).Nodup := by
    rw [hforward, hlha_coordVertices_take]
    exact hfullNodup.take
  have habsNodup :
      (hlha_edgeVertices r.pos (hlha_negCoord r.dir)
        (loopReverse us)).Nodup := by
    rw [hrev.1]
    exact List.nodup_reverse.mpr hforwardNodup
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us)
  simp only [hlha_add_zero] at htrans
  have hrelNodup :
      (hlha_edgeVertices HexReturnCoord.zero (hlha_negCoord r.dir)
        (loopReverse us)).Nodup := by
    rw [htrans] at habsNodup
    exact habsNodup.of_map
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us) hrevLegal
  simp only [hlha_negCoord_zero, hlha_negCoord_negCoord] at hneg
  have hnormNodup :
      (hlha_edgeVertices HexReturnCoord.zero r.dir
        (loopReverse us)).Nodup := by
    rw [hneg]
    exact hrelNodup.map hlha_negCoord_injective
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  change (hlhc_prefixCoord ts hleg.1 cp).color = .white at hcutWhite
  have hscore : ∀ q ∈ hlha_edgeVertices HexReturnCoord.zero r.dir
      (loopReverse us), -2 ≤ hlhda_score q := by
    intro q hq
    obtain ⟨k, hk, hqeq⟩ :=
      hlhda_prefix_normalized_point hleg hpre hq
    rw [hqeq]
    apply hlhda_normalized_score_lower _ _ hcutWhite
    exact hlhda_cutPos_max ts hleg k
      (le_trans hk (hlhda_cutPos_le ts hleg))
  have hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero r.dir (loopReverse us) := by
    intro hmem
    obtain ⟨k, hk, hqeq⟩ :=
      hlhda_prefix_normalized_point hleg hpre hmem
    have hneighbor := (hlhda_normalized_eq_flat_iff
      (hlhc_prefixCoord ts hleg.1 cp)
      (hlhc_prefixCoord ts hleg.1 k) hcutWhite).mp hqeq.symm
    have hdepthEq : hlhd_depth ts hleg k = hlhd_depth ts hleg cp := by
      unfold hlhd_depth
      rw [hneighbor, hlhda_depth_neighbor_zero]
    have hklt : k < cp := by
      apply lt_of_le_of_ne hk
      intro hkeq
      subst k
      have hz := hlha_add_neg_self
        (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp))
      rw [hz] at hqeq
      exact (by decide : hlhda_flatNeighbor ≠ HexReturnCoord.zero) hqeq
    have hfirst := hlhda_cutPos_first ts hleg k hklt
    change hlhd_depth ts hleg k < hlhd_depth ts hleg cp at hfirst
    omega
  exact ⟨hlhda_cutState_inward hleg hne, hrevLegal, hnormNodup,
    hscore, hflat⟩

noncomputable def hlhda_prefixAugment (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ :=
  match hpre : ts.take (hlhda_cutPos ts hleg) with
  | [] => hlhda_emptySide
  | _ :: us => hlhda_augmentSide (hlhda_cutState ts hleg).dir
      (loopReverse us)

theorem hlhda_prefixAugment_isLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_prefixAugment ts hleg)).IsLegalSAW := by
  unfold hlhda_prefixAugment
  split
  · exact hlhda_emptySide_isLegalSAW
  · rename_i t us hpre
    have hne : ts ≠ [] := by
      intro hnil
      simp [hnil] at hpre
    obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
      hlhda_prefix_side_hypotheses hleg hne hpre
    exact hlhda_augmentSide_isLegalSAW _ _ hd hlegal hnodup hscore hflat

theorem hlhda_prefixAugment_halfSpace (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    HLHDLiteralHalfSpace (hlhda_prefixAugment ts hleg)
      (hlhda_prefixAugment_isLegalSAW ts hleg) := by
  by_cases hpre : ts.take (hlhda_cutPos ts hleg) = []
  · have hout : hlhda_prefixAugment ts hleg = hlhda_emptySide := by
      unfold hlhda_prefixAugment
      split <;> simp_all
    exact hlhda_halfSpace_congr hout.symm hlhda_emptySide_halfSpace
  · obtain ⟨t, us, hpreEq⟩ := List.exists_cons_of_ne_nil hpre
    have hout : hlhda_prefixAugment ts hleg =
        hlhda_augmentSide (hlhda_cutState ts hleg).dir
          (loopReverse us) := by
      unfold hlhda_prefixAugment
      split <;> simp_all
    have hne : ts ≠ [] := by
      intro hnil
      simp [hnil] at hpreEq
    obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
      hlhda_prefix_side_hypotheses hleg hne hpreEq
    apply hlhda_halfSpace_congr hout.symm
    exact hlhda_augmentSide_halfSpace _ _ hd hlegal hnodup hscore hflat

theorem hlhda_prefixAugment_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_prefixAugment ts hleg).length = hlhda_cutPos ts hleg + 2 := by
  unfold hlhda_prefixAugment
  split
  · rename_i hpre
    have hlen := congrArg List.length hpre
    simp only [List.length_take, List.length_nil] at hlen
    have hcple := hlhda_cutPos_le ts hleg
    simp only [hlhda_emptySide_length]
    omega
  · rename_i t us hpre
    rw [hlhda_augmentSide_length]
    have hlen := congrArg List.length hpre
    rw [List.length_take_of_le (hlhda_cutPos_le ts hleg)] at hlen
    simp only [List.length_cons] at hlen
    simp [loopReverse]
    omega

theorem hlhda_prefixAugment_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_prefixAugment ts hleg)).IsLegalSAW ∧
      HLHDLiteralHalfSpace (hlhda_prefixAugment ts hleg)
        (hlhda_prefixAugment_isLegalSAW ts hleg) ∧
      (hlhda_prefixAugment ts hleg).length =
        hlhda_cutPos ts hleg + 2 :=
  ⟨hlhda_prefixAugment_isLegalSAW ts hleg,
    hlhda_prefixAugment_halfSpace ts hleg,
    hlhda_prefixAugment_length ts hleg⟩



theorem hlhda_coordVertices_getElem (p d : HexReturnCoord) (ts : List ℤ)
    (k : ℕ) (hk : k ≤ ts.length) :
    (hlha_coordVertices p d ts)[k]'(by
      rw [hlha_coordVertices_length]
      omega) = (hlhr_coordRun p d (ts.take k)).pos := by
  induction ts generalizing p d k with
  | nil =>
      have hk0 : k = 0 := by simpa using hk
      subst k
      simp [hlha_coordVertices, hlhr_coordRun]
  | cons t ts ih =>
      cases k with
      | zero => simp [hlha_coordVertices, hlhr_coordRun]
      | succ k =>
          simp only [hlha_coordVertices, List.getElem_cons_succ,
            List.take_succ_cons, hlhr_coordRun]
          exact ih (p.add (d.turn t)) (d.turn t) k (by
            simp only [List.length_cons] at hk
            omega)

theorem hlhda_prefixCoord_injective (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {k l : ℕ} (hk : k ≤ ts.length) (hl : l ≤ ts.length)
    (heq : hlhc_prefixCoord ts hleg.1 k =
      hlhc_prefixCoord ts hleg.1 l) : k = l := by
  let vs := hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts
  have hnd : vs.Nodup := hlha_source_coord_nodup hexAWStart 1 ts hleg
  have hklen : k < vs.length := by
    dsimp [vs]
    rw [hlha_coordVertices_length]
    omega
  have hllen : l < vs.length := by
    dsimp [vs]
    rw [hlha_coordVertices_length]
    omega
  apply (hnd.getElem_inj_iff (hi := hklen) (hj := hllen)).mp
  rw [hlhda_coordVertices_getElem _ _ _ k hk,
    hlhda_coordVertices_getElem _ _ _ l hl,
    hlhda_prefixCoord_returnPos ts hleg k,
    hlhda_prefixCoord_returnPos ts hleg l, heq]

theorem hlhda_cut_next_state {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us) :
    hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (ts.take (hlhda_cutPos ts hleg + 1)) =
      let r := hlhda_cutState ts hleg
      ⟨r.pos.add (r.dir.turn t), r.dir.turn t⟩ := by
  let cp := hlhda_cutPos ts hleg
  have hcplt : cp < ts.length := by
    have hlen := congrArg List.length hsuf
    simp only [List.length_drop, List.length_cons] at hlen
    omega
  have hdrop := List.drop_eq_getElem_cons hcplt
  rw [hsuf] at hdrop
  have htget : ts[cp] = t := by
    exact List.cons.inj hdrop |>.1.symm
  have htake := List.take_concat_get' ts cp hcplt
  rw [htget] at htake
  rw [← htake, hlha_coordRun_append]
  simp [hlhda_cutState, cp, hlhr_coordRun]

theorem hlhda_normalized_neighbor_cases (source : HexAWCoord)
    (hs : source.color = .white) (e : Fin 3) :
    let q := (hexAWReturnPos source).add
      (hlha_negCoord (hexAWReturnPos (hexAWNeighbor source e)))
    q = hlhda_flatNeighbor ∨ HLHDAInwardDir q := by
  rcases source with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;>
    simp [hexAWReturnPos, hexAWNeighbor, HexReturnCoord.add,
      hlha_negCoord, hlhda_flatNeighbor, HLHDAInwardDir,
      HexReturnCoord.base, HexReturnCoord.turn, HexReturnCoord.left,
      HexReturnCoord.right] <;> ring

theorem hlhda_suffix_normalized_point {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
    {q : HexReturnCoord}
    (hq : q ∈ hlha_edgeVertices HexReturnCoord.zero
      (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us) :
    ∃ k, k ≤ ts.length ∧
      q = (hexAWReturnPos
          (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add
        (hlha_negCoord (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k))) := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := r.dir.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_drop
    rw [hsuf]
    simp
  have ht := hleg.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hudrop : u ∈ ts.drop (hlhda_cutPos ts hleg) := by
      rw [hsuf]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_drop hudrop)
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero d0 us hus
  simp only [hlha_negCoord_zero] at hneg
  rw [hneg, List.mem_map] at hq
  obtain ⟨p, hp, hqp⟩ := hq
  have hdrop := hlha_coordVertices_drop HexReturnCoord.zero
    HexReturnCoord.base ts cp (hlhda_cutPos_le ts hleg)
  rw [hsuf] at hdrop
  change hlha_coordVertices r.pos r.dir (t :: us) = _ at hdrop
  rw [hlha_coordVertices_cons_eq_edge] at hdrop
  change hlha_edgeVertices r.pos d0 us = _ at hdrop
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero d0 us
  simp only [hlha_add_zero] at htrans
  have habs : r.pos.add p ∈
      hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts := by
    apply List.mem_of_mem_drop
    rw [← hdrop, htrans, List.mem_map]
    exact ⟨p, hp, rfl⟩
  obtain ⟨k, hk, hkpos⟩ := hlha_mem_coordVertices
    HexReturnCoord.zero HexReturnCoord.base ts habs
  have hkReturn := hlhda_prefixCoord_returnPos ts hleg k
  have hcpReturn := hlhda_prefixCoord_returnPos ts hleg cp
  refine ⟨k, hk, ?_⟩
  rw [← hkReturn, ← hcpReturn, ← hqp, ← hkpos]
  change hlha_negCoord p = r.pos.add (hlha_negCoord (r.pos.add p))
  exact (hlhda_add_neg_add r.pos p).symm

theorem hlhda_suffix_flat_forces_terminal {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ [])
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
    (hflat : hlhda_flatNeighbor ∈
      hlha_edgeVertices HexReturnCoord.zero
        (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us) :
    us = [] := by
  let cp := hlhda_cutPos ts hleg
  let cut := hlhc_prefixCoord ts hleg.1 cp
  obtain ⟨k, hk, hkflat⟩ :=
    hlhda_suffix_normalized_point hleg hsuf hflat
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  change cut.color = .white at hcutWhite
  have hkCoord : hlhc_prefixCoord ts hleg.1 k = hexAWNeighbor cut 0 :=
    (hlhda_normalized_eq_flat_iff cut
      (hlhc_prefixCoord ts hleg.1 k) hcutWhite).mp hkflat.symm
  have hkDepth : hlhd_depth ts hleg k = hlhd_depth ts hleg cp := by
    unfold hlhd_depth
    rw [hkCoord, hlhda_depth_neighbor_zero]
  have hcpLe := hlhda_cutPos_le ts hleg
  have hkgt : cp < k := by
    rcases lt_trichotomy k cp with hlt | heq | hgt
    · have hfirst := hlhda_cutPos_first ts hleg k hlt
      change hlhd_depth ts hleg k < hlhd_depth ts hleg cp at hfirst
      omega
    · subst k
      exact (hexAWNeighbor_ne cut 0 hkCoord.symm).elim
    · exact hgt
  have hkPos : 0 < k := lt_trans (hlhda_cutPos_pos hleg hne) hkgt
  have hkm1lt : k - 1 < ts.length := by omega
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg (k - 1) hkm1lt
  have hksucc : k - 1 + 1 = k := by omega
  rw [hksucc, hkCoord] at he
  have hback := congrArg (fun c => hexAWNeighbor c e) he
  simp only [hexAWNeighbor_invol] at hback
  have hcases := hlhd_neighbor_depth_cases (hexAWNeighbor cut 0) e
  have hprevMax := hlhda_cutPos_max ts hleg (k - 1) (by omega)
  change hlhd_depth ts hleg (k - 1) ≤ hlhd_depth ts hleg cp at hprevMax
  have hprevCoord : hlhc_prefixCoord ts hleg.1 (k - 1) = cut := by
    rcases hcases with hinc | hdec | hzero
    · have hdepthInc : hlhd_depth ts hleg (k - 1) =
          hlhd_depth ts hleg cp + 1 := by
        unfold hlhd_depth
        rw [hback, hinc.1, hlhda_depth_neighbor_zero]
      omega
    · have hblack : (hexAWNeighbor cut 0).color = .black :=
        hlhda_neighbor_color_white hcutWhite rfl
      have hcolor := hdec.2.1
      rw [hblack] at hcolor
      cases hcolor
    · rw [hzero.2] at hback
      simpa using hback
  have hkm1 : k - 1 = cp :=
    hlhda_prefixCoord_injective ts hleg (by omega) hcpLe hprevCoord
  have hkEq : k = cp + 1 := by omega
  have hkLast : k = ts.length := by
    by_contra hneLast
    have hklt : k < ts.length := by omega
    obtain ⟨f, hf⟩ := hlhc_prefixCoord_adjacent ts hleg k hklt
    rw [hkCoord] at hf
    have hfcases := hlhd_neighbor_depth_cases (hexAWNeighbor cut 0) f
    have hnextMax := hlhda_cutPos_max ts hleg (k + 1) (by omega)
    change hlhd_depth ts hleg (k + 1) ≤ hlhd_depth ts hleg cp at hnextMax
    rcases hfcases with hinc | hdec | hzero
    · have hnextDepth : hlhd_depth ts hleg (k + 1) =
          hlhd_depth ts hleg cp + 1 := by
        unfold hlhd_depth
        rw [← hf, hinc.1, hlhda_depth_neighbor_zero]
      omega
    · have hblack : (hexAWNeighbor cut 0).color = .black :=
        hlhda_neighbor_color_white hcutWhite rfl
      have hcolor := hdec.2.1
      rw [hblack] at hcolor
      cases hcolor
    · have hnextCut : hlhc_prefixCoord ts hleg.1 (k + 1) = cut := by
        rw [hzero.2] at hf
        simpa using hf.symm
      have : k + 1 = cp :=
        hlhda_prefixCoord_injective ts hleg (by omega) hcpLe hnextCut
      omega
  have hsufLen := congrArg List.length hsuf
  simp only [List.length_drop, List.length_cons] at hsufLen
  have husLen : us.length = 0 := by omega
  exact List.length_eq_zero_iff.mp husLen

theorem hlhda_inward_empty_hypotheses (d : HexReturnCoord)
    (hd : HLHDAInwardDir d) :
    (hlha_edgeVertices HexReturnCoord.zero d []).Nodup ∧
      (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d [],
        -2 ≤ hlhda_score q) ∧
      hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d [] := by
  rcases hd with hd | hd <;> rw [hd] <;>
    simp [hlha_edgeVertices, HexReturnCoord.zero, HexReturnCoord.base,
      HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.right,
      HexReturnCoord.add, hlhda_score, hlhda_flatNeighbor]

theorem hlhda_suffix_side_hypotheses {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
    (hnotFlat : hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) ≠
      hlhda_flatNeighbor) :
    let d := hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)
    HLHDAInwardDir d ∧
      (∀ u ∈ us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d us).Nodup ∧
      (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d us,
        -2 ≤ hlhda_score q) ∧
      hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d us := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := r.dir.turn t
  let d := hlha_negCoord d0
  have hne : ts ≠ [] := by
    intro hnil
    simp [hnil] at hsuf
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_drop
    rw [hsuf]
    simp
  have ht := hleg.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hudrop : u ∈ ts.drop (hlhda_cutPos ts hleg) := by
      rw [hsuf]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_drop hudrop)
  have hdrop := hlha_coordVertices_drop HexReturnCoord.zero
    HexReturnCoord.base ts cp (hlhda_cutPos_le ts hleg)
  rw [hsuf] at hdrop
  change hlha_coordVertices r.pos r.dir (t :: us) = _ at hdrop
  rw [hlha_coordVertices_cons_eq_edge] at hdrop
  change hlha_edgeVertices r.pos d0 us = _ at hdrop
  have habsNodup : (hlha_edgeVertices r.pos d0 us).Nodup := by
    rw [hdrop]
    exact (hlha_source_coord_nodup hexAWStart 1 ts hleg).drop
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero d0 us
  simp only [hlha_add_zero] at htrans
  have hrelNodup :
      (hlha_edgeVertices HexReturnCoord.zero d0 us).Nodup := by
    rw [htrans] at habsNodup
    exact habsNodup.of_map
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero d0 us hus
  simp only [hlha_negCoord_zero] at hneg
  have hnormNodup :
      (hlha_edgeVertices HexReturnCoord.zero d us).Nodup := by
    change (hlha_edgeVertices HexReturnCoord.zero
      (hlha_negCoord d0) us).Nodup
    rw [hneg]
    exact hrelNodup.map hlha_negCoord_injective
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  change (hlhc_prefixCoord ts hleg.1 cp).color = .white at hcutWhite
  have hscore : ∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d us,
      -2 ≤ hlhda_score q := by
    intro q hq
    obtain ⟨k, hk, hqeq⟩ := hlhda_suffix_normalized_point hleg hsuf hq
    rw [hqeq]
    apply hlhda_normalized_score_lower _ _ hcutWhite
    exact hlhda_cutPos_max ts hleg k hk
  have hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d us := by
    intro hmem
    have husNil := hlhda_suffix_flat_forces_terminal hleg hne hsuf hmem
    subst us
    simp [hlha_edgeVertices, hlha_zero_add] at hmem
    rcases hmem with hzero | hdflat
    · exact (by decide : HexReturnCoord.zero ≠ hlhda_flatNeighbor) hzero.symm
    · exact hnotFlat hdflat.symm
  have hcplt : cp < ts.length := by
    have hlen := congrArg List.length hsuf
    simp only [List.length_drop, List.length_cons] at hlen
    omega
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg cp hcplt
  have hnext := hlhda_cut_next_state hleg hsuf
  have hnextPos := congrArg HLHRCoordRun.pos hnext
  have hrPos := hlhda_prefixCoord_returnPos ts hleg cp
  change r.pos = hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp) at hrPos
  have hnPos := hlhda_prefixCoord_returnPos ts hleg (cp + 1)
  have hdCoord : d =
      (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp)).add
        (hlha_negCoord
          (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (cp + 1)))) := by
    change hlha_negCoord d0 = _
    change (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
      (ts.take (cp + 1))).pos = r.pos.add d0 at hnextPos
    rw [hnPos, hrPos] at hnextPos
    rw [hnextPos, ← hrPos]
    exact (hlhda_add_neg_add r.pos d0).symm
  have hdirCases := hlhda_normalized_neighbor_cases
    (hlhc_prefixCoord ts hleg.1 cp) hcutWhite e
  rw [he] at hdirCases
  change _ = hlhda_flatNeighbor ∨ HLHDAInwardDir _ at hdirCases
  rw [← hdCoord] at hdirCases
  have hdInward : HLHDAInwardDir d := hdirCases.resolve_left hnotFlat
  exact ⟨hdInward, hus, hnormNodup, hscore, hflat⟩

noncomputable def hlhda_suffixAugment (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ :=
  match hsuf : ts.drop (hlhda_cutPos ts hleg) with
  | [] => hlhda_emptySide
  | t :: us =>
      if hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) =
          hlhda_flatNeighbor then
        hlhda_augmentSide (hlhda_cutState ts hleg).dir []
      else
        hlhda_augmentSide
          (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us

theorem hlhda_suffixAugment_isLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_suffixAugment ts hleg)).IsLegalSAW := by
  unfold hlhda_suffixAugment
  split
  · exact hlhda_emptySide_isLegalSAW
  · rename_i t us hsuf
    split
    · rename_i hflat
      have hne : ts ≠ [] := by intro hnil; simp [hnil] at hsuf
      have hd := hlhda_cutState_inward hleg hne
      obtain ⟨hnodup, hscore, havoid⟩ :=
        hlhda_inward_empty_hypotheses _ hd
      exact hlhda_augmentSide_isLegalSAW _ [] hd (by simp) hnodup
        hscore havoid
    · rename_i hnotFlat
      obtain ⟨hd, hlegal, hnodup, hscore, havoid⟩ :=
        hlhda_suffix_side_hypotheses hleg hsuf hnotFlat
      exact hlhda_augmentSide_isLegalSAW _ us hd hlegal hnodup
        hscore havoid

theorem hlhda_suffixAugment_halfSpace (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    HLHDLiteralHalfSpace (hlhda_suffixAugment ts hleg)
      (hlhda_suffixAugment_isLegalSAW ts hleg) := by
  cases hsuf : ts.drop (hlhda_cutPos ts hleg) with
  | nil =>
    have hout : hlhda_suffixAugment ts hleg = hlhda_emptySide := by
      unfold hlhda_suffixAugment
      split <;> simp_all
    exact hlhda_halfSpace_congr hout.symm hlhda_emptySide_halfSpace
  | cons t us =>
    by_cases hflat :
        hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) =
          hlhda_flatNeighbor
    · have hout : hlhda_suffixAugment ts hleg =
          hlhda_augmentSide (hlhda_cutState ts hleg).dir [] := by
        unfold hlhda_suffixAugment
        split <;> simp_all
      have hne : ts ≠ [] := by intro hnil; simp [hnil] at hsuf
      have hd := hlhda_cutState_inward hleg hne
      obtain ⟨hnodup, hscore, havoid⟩ :=
        hlhda_inward_empty_hypotheses _ hd
      apply hlhda_halfSpace_congr hout.symm
      exact hlhda_augmentSide_halfSpace _ [] hd (by simp) hnodup
        hscore havoid
    · have hout : hlhda_suffixAugment ts hleg =
          hlhda_augmentSide
            (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us := by
        unfold hlhda_suffixAugment
        split <;> simp_all
      obtain ⟨hd, hlegal, hnodup, hscore, havoid⟩ :=
        hlhda_suffix_side_hypotheses hleg hsuf hflat
      apply hlhda_halfSpace_congr hout.symm
      exact hlhda_augmentSide_halfSpace _ us hd hlegal hnodup
        hscore havoid

theorem hlhda_suffixAugment_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_suffixAugment ts hleg).length =
      (ts.drop (hlhda_cutPos ts hleg)).length + 2 := by
  unfold hlhda_suffixAugment
  split
  · rename_i hsuf
    have hlen := congrArg List.length hsuf
    simp only [List.length_drop, List.length_nil] at hlen
    simp [hlen]
  · rename_i t us hsuf
    split
    · rename_i hflat
      have hne : ts ≠ [] := by intro hnil; simp [hnil] at hsuf
      have hdmem : hlhda_flatNeighbor ∈
          hlha_edgeVertices HexReturnCoord.zero
            (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us := by
        rw [← hflat]
        exact hlhda_firstDir_mem_edgeVertices _ us
      have husNil := hlhda_suffix_flat_forces_terminal hleg hne hsuf hdmem
      subst us
      have hlen := congrArg List.length hsuf
      simp only [List.length_drop, List.length_cons, List.length_nil] at hlen
      simp [hlen]
    · have hlen := congrArg List.length hsuf
      simp only [List.length_drop, List.length_cons] at hlen
      simp [hlen]

theorem hlhda_suffixAugment_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_suffixAugment ts hleg)).IsLegalSAW ∧
      HLHDLiteralHalfSpace (hlhda_suffixAugment ts hleg)
        (hlhda_suffixAugment_isLegalSAW ts hleg) ∧
      (hlhda_suffixAugment ts hleg).length =
        (ts.drop (hlhda_cutPos ts hleg)).length + 2 :=
  ⟨hlhda_suffixAugment_isLegalSAW ts hleg,
    hlhda_suffixAugment_halfSpace ts hleg,
    hlhda_suffixAugment_length ts hleg⟩



theorem hlhda_entryTurn_injective_on_inward {d e : HexReturnCoord}
    (hd : HLHDAInwardDir d) (he : HLHDAInwardDir e)
    (h : hlhda_entryTurn d = hlhda_entryTurn e) : d = e := by
  rcases hd with hd | hd <;> rcases he with he | he <;>
    rw [hd, he] at h ⊢ <;>
    simp [hlhda_entryTurn, HexReturnCoord.base, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] at h ⊢

theorem hlhda_inward_ne_flat {d : HexReturnCoord} (hd : HLHDAInwardDir d) :
    d ≠ hlhda_flatNeighbor := by
  rcases hd with hd | hd <;> rw [hd] <;>
    decide

theorem hlhda_coordRun_dir_pos_independent (p q d : HexReturnCoord)
    (ts : List ℤ) :
    (hlhr_coordRun p d ts).dir = (hlhr_coordRun q d ts).dir := by
  induction ts generalizing p q d with
  | nil => rfl
  | cons t ts ih =>
      simpa [hlhr_coordRun] using
        ih (p.add (d.turn t)) (q.add (d.turn t)) (d.turn t)

noncomputable def hlhda_reverseCode (xs : List ℤ) : List ℤ :=
  match xs with
  | [] => hlhda_emptySide
  | _ :: us =>
      hlhda_augmentSide
        (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir
        (loopReverse us)

theorem hlhda_prefixAugment_eq_reverseCode (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_prefixAugment ts hleg =
      hlhda_reverseCode (ts.take (hlhda_cutPos ts hleg)) := by
  unfold hlhda_prefixAugment
  split
  · rename_i hpre
    rw [hpre]
    rfl
  · rename_i t us hpre
    rw [hpre]
    unfold hlhda_reverseCode hlhda_cutState
    rw [hpre]

theorem hlhda_reverseCode_injective {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxin : xs ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir)
    (hyin : ys ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ys).dir)
    (heq : hlhda_reverseCode xs = hlhda_reverseCode ys) : xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlhda_reverseCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlhda_reverseCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
      | cons y ys =>
          let rx := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (x :: xs)
          let ry := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (y :: ys)
          have hdx := hxin (by simp)
          have hdy := hyin (by simp)
          change hlhda_augmentSide rx.dir (loopReverse xs) =
            hlhda_augmentSide ry.dir (loopReverse ys) at heq
          have hentry : hlhda_entryTurn rx.dir = hlhda_entryTurn ry.dir := by
            have hget := congrArg (fun l : List ℤ => l[2]?) heq
            simpa [hlhda_augmentSide] using hget
          have hdir : rx.dir = ry.dir :=
            hlhda_entryTurn_injective_on_inward hdx hdy hentry
          have htail : loopReverse xs = loopReverse ys := by
            have hdrop := congrArg (List.drop 3) heq
            simpa [hlhda_augmentSide] using hdrop
          have hxyTail : xs = ys := hlha_loopReverse_injective htail
          subst ys
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          let dx := HexReturnCoord.base.turn x
          let dy := HexReturnCoord.base.turn y
          have hrx := hlha_edgeVertices_loopReverse HexReturnCoord.zero dx xs
            (by intro u hu; exact hxlegal u (by simp [hu]))
          have hry := hlha_edgeVertices_loopReverse HexReturnCoord.zero dy xs
            (by intro u hu; exact hylegal u (by simp [hu]))
          have hrxState :
              hlhr_coordRun (HexReturnCoord.zero.add dx) dx xs = rx := by
            rfl
          have hryState :
              hlhr_coordRun (HexReturnCoord.zero.add dy) dy xs = ry := by
            rfl
          rw [hrxState] at hrx
          rw [hryState] at hry
          have hfinalDir : hlha_negCoord dx = hlha_negCoord dy := by
            have hrunDir := hlhda_coordRun_dir_pos_independent
              (rx.pos.add (hlha_negCoord rx.dir))
              (ry.pos.add (hlha_negCoord ry.dir))
              (hlha_negCoord rx.dir) (loopReverse xs)
            have hrxEnd :
                hlhr_coordRun (rx.pos.add (hlha_negCoord rx.dir))
                    (hlha_negCoord rx.dir) (loopReverse xs) =
                  { pos := HexReturnCoord.zero,
                    dir := hlha_negCoord dx } := by
              simpa using hrx.2
            have hryEnd :
                hlhr_coordRun (ry.pos.add (hlha_negCoord ry.dir))
                    (hlha_negCoord ry.dir) (loopReverse xs) =
                  { pos := HexReturnCoord.zero,
                    dir := hlha_negCoord dy } := by
              simpa using hry.2
            rw [← hdir] at hrunDir hryEnd
            have hxFinal := congrArg HLHRCoordRun.dir hrxEnd
            have hyFinal := congrArg HLHRCoordRun.dir hryEnd
            exact hxFinal.symm.trans (hrunDir.trans hyFinal)
          have hdxy : dx = dy := hlha_negCoord_injective hfinalDir
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
            simp [dx, dy, HexReturnCoord.base, HexReturnCoord.turn,
              HexReturnCoord.left, HexReturnCoord.right] at hdxy ⊢

def hlhda_forwardEncodedDir (incoming : HexReturnCoord) (t : ℤ) :
    HexReturnCoord :=
  let d := hlha_negCoord (incoming.turn t)
  if d = hlhda_flatNeighbor then incoming else d

noncomputable def hlhda_forwardCode (incoming : HexReturnCoord)
    (xs : List ℤ) : List ℤ :=
  match xs with
  | [] => hlhda_emptySide
  | t :: us =>
      hlhda_augmentSide (hlhda_forwardEncodedDir incoming t)
        (if hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor then [] else us)

theorem hlhda_suffixAugment_eq_forwardCode (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_suffixAugment ts hleg =
      hlhda_forwardCode (hlhda_cutState ts hleg).dir
        (ts.drop (hlhda_cutPos ts hleg)) := by
  unfold hlhda_suffixAugment
  split
  · rename_i hsuf
    rw [hsuf]
    rfl
  · rename_i t us hsuf
    by_cases hflat :
        hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) =
          hlhda_flatNeighbor
    · rw [hsuf]
      simp [hlhda_forwardCode, hlhda_forwardEncodedDir, hflat]
    · rw [hsuf]
      simp [hlhda_forwardCode, hlhda_forwardEncodedDir, hflat]

theorem hlhda_forwardEncodedDir_injective
    (incoming : HexReturnCoord) (hin : HLHDAInwardDir incoming)
    {t u : ℤ} (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1)
    (hdt : hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨
      HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
    (hdu : hlha_negCoord (incoming.turn u) = hlhda_flatNeighbor ∨
      HLHDAInwardDir (hlha_negCoord (incoming.turn u)))
    (heq : hlhda_forwardEncodedDir incoming t =
      hlhda_forwardEncodedDir incoming u) : t = u := by
  rcases hin with hin | hin <;> rcases ht with rfl | rfl <;>
    rcases hu with rfl | rfl <;>
    simp [hlhda_forwardEncodedDir, hin, hlha_negCoord,
      hlhda_flatNeighbor, HexReturnCoord.base, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] at hdt hdu heq ⊢

theorem hlhda_forwardCode_injective (incoming : HexReturnCoord)
    (hin : HLHDAInwardDir incoming) {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxdir : ∀ t us, xs = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨
        HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
    (hydir : ∀ t us, ys = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨
        HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
    (hxflat : ∀ t us, xs = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor → us = [])
    (hyflat : ∀ t us, ys = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor → us = [])
    (heq : hlhda_forwardCode incoming xs = hlhda_forwardCode incoming ys) :
    xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlhda_forwardCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlhda_forwardCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
      | cons y ys =>
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          have hxd := hxdir x xs rfl
          have hyd := hydir y ys rfl
          change hlhda_augmentSide (hlhda_forwardEncodedDir incoming x)
              (if hlha_negCoord (incoming.turn x) = hlhda_flatNeighbor
                then [] else xs) =
            hlhda_augmentSide (hlhda_forwardEncodedDir incoming y)
              (if hlha_negCoord (incoming.turn y) = hlhda_flatNeighbor
                then [] else ys) at heq
          have hentry : hlhda_entryTurn (hlhda_forwardEncodedDir incoming x) =
              hlhda_entryTurn (hlhda_forwardEncodedDir incoming y) := by
            have hget := congrArg (fun l : List ℤ => l[2]?) heq
            simpa [hlhda_augmentSide] using hget
          have hencInX : HLHDAInwardDir
              (hlhda_forwardEncodedDir incoming x) := by
            rcases hxd with hflat | hd
            · simpa [hlhda_forwardEncodedDir, hflat] using hin
            · have hne := hlhda_inward_ne_flat hd
              simpa [hlhda_forwardEncodedDir, hne] using hd
          have hencInY : HLHDAInwardDir
              (hlhda_forwardEncodedDir incoming y) := by
            rcases hyd with hflat | hd
            · simpa [hlhda_forwardEncodedDir, hflat] using hin
            · have hne := hlhda_inward_ne_flat hd
              simpa [hlhda_forwardEncodedDir, hne] using hd
          have hencEq := hlhda_entryTurn_injective_on_inward
            hencInX hencInY hentry
          have hxy := hlhda_forwardEncodedDir_injective incoming hin hx hy
            hxd hyd hencEq
          subst y
          by_cases hflat :
              hlha_negCoord (incoming.turn x) = hlhda_flatNeighbor
          · rw [hxflat x xs rfl hflat, hyflat x ys rfl hflat]
          · have hdrop := congrArg (List.drop 3) heq
            simpa [hlhda_augmentSide, hlhda_forwardEncodedDir, hflat] using hdrop

noncomputable def hlhda_augmentedPair (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ × List ℤ :=
  (hlhda_prefixAugment ts hleg, hlhda_suffixAugment ts hleg)

theorem hlhda_augmentedPair_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_augmentedPair ts hleg).1.length +
        (hlhda_augmentedPair ts hleg).2.length = ts.length + 4 := by
  rw [hlhda_augmentedPair, hlhda_prefixAugment_length,
    hlhda_suffixAugment_length]
  have hcple := hlhda_cutPos_le ts hleg
  simp only [List.length_drop]
  omega

theorem hlhda_augmentedPair_injective
    {xs ys : List ℤ}
    (hx : (ofTurns hexAWStart 1 xs).IsLegalSAW)
    (hy : (ofTurns hexAWStart 1 ys).IsLegalSAW)
    (heq : hlhda_augmentedPair xs hx = hlhda_augmentedPair ys hy) :
    xs = ys := by
  let cpx := hlhda_cutPos xs hx
  let cpy := hlhda_cutPos ys hy
  let px := xs.take cpx
  let py := ys.take cpy
  have hpreCode : hlhda_reverseCode px = hlhda_reverseCode py := by
    have hfst := congrArg Prod.fst heq
    rw [hlhda_augmentedPair, hlhda_augmentedPair,
      hlhda_prefixAugment_eq_reverseCode,
      hlhda_prefixAugment_eq_reverseCode] at hfst
    exact hfst
  have hxpreLegal : ∀ t ∈ px, t = 1 ∨ t = -1 := by
    intro t ht
    exact hx.1 t (List.mem_of_mem_take ht)
  have hypreLegal : ∀ t ∈ py, t = 1 ∨ t = -1 := by
    intro t ht
    exact hy.1 t (List.mem_of_mem_take ht)
  have hxpreIn : px ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base px).dir := by
    intro hpx
    have hxne : xs ≠ [] := by intro hnil; simp [px, hnil] at hpx
    simpa [px, cpx, hlhda_cutState] using hlhda_cutState_inward hx hxne
  have hypreIn : py ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base py).dir := by
    intro hpy
    have hyne : ys ≠ [] := by intro hnil; simp [py, hnil] at hpy
    simpa [py, cpy, hlhda_cutState] using hlhda_cutState_inward hy hyne
  have hpre : px = py := hlhda_reverseCode_injective hxpreLegal
    hypreLegal hxpreIn hypreIn hpreCode
  have hpxLen : px.length = cpx := by
    simp [px, cpx, List.length_take_of_le (hlhda_cutPos_le xs hx)]
  have hpyLen : py.length = cpy := by
    simp [py, cpy, List.length_take_of_le (hlhda_cutPos_le ys hy)]
  have hcp : cpx = cpy := by rw [← hpxLen, ← hpyLen, hpre]
  by_cases hpxNil : px = []
  · have hxNil : xs = [] := by
      by_contra hxne
      have hcpos := hlhda_cutPos_pos hx hxne
      have hlen := congrArg List.length hpxNil
      rw [hpxLen] at hlen
      simp at hlen
      change 0 < cpx at hcpos
      omega
    have hpyNil : py = [] := hpre ▸ hpxNil
    have hyNil : ys = [] := by
      by_contra hyne
      have hcpos := hlhda_cutPos_pos hy hyne
      have hlen := congrArg List.length hpyNil
      rw [hpyLen] at hlen
      simp at hlen
      change 0 < cpy at hcpos
      omega
    rw [hxNil, hyNil]
  · have hxne : xs ≠ [] := by intro hnil; simp [px, hnil] at hpxNil
    have hyne : ys ≠ [] := by
      intro hnil
      have : py = [] := by simp [py, hnil]
      exact hpxNil (hpre.trans this)
    let r := hlhda_cutState xs hx
    have hr : hlhda_cutState ys hy = r := by
      dsimp [r, hlhda_cutState]
      change hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base py =
        hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base px
      rw [hpre]
    let sx := xs.drop cpx
    let sy := ys.drop cpy
    have hsufCode : hlhda_forwardCode r.dir sx =
        hlhda_forwardCode r.dir sy := by
      have hsnd := congrArg Prod.snd heq
      rw [hlhda_augmentedPair, hlhda_augmentedPair,
        hlhda_suffixAugment_eq_forwardCode,
        hlhda_suffixAugment_eq_forwardCode] at hsnd
      simpa [sx, sy, cpx, cpy, r, hr] using hsnd
    have hrIn : HLHDAInwardDir r.dir := hlhda_cutState_inward hx hxne
    have hsxLegal : ∀ t ∈ sx, t = 1 ∨ t = -1 := by
      intro t ht
      exact hx.1 t (List.mem_of_mem_drop ht)
    have hsyLegal : ∀ t ∈ sy, t = 1 ∨ t = -1 := by
      intro t ht
      exact hy.1 t (List.mem_of_mem_drop ht)
    have hsxDir : ∀ t us, sx = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor ∨
          HLHDAInwardDir (hlha_negCoord (r.dir.turn t)) := by
      intro t us hs
      by_cases hflat : hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor
      · exact Or.inl hflat
      · exact Or.inr (hlhda_suffix_side_hypotheses hx
          (by simpa [sx, cpx] using hs) hflat).1
    have hsyDir : ∀ t us, sy = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor ∨
          HLHDAInwardDir (hlha_negCoord (r.dir.turn t)) := by
      intro t us hs
      by_cases hflat : hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor
      · exact Or.inl hflat
      · have hh := hlhda_suffix_side_hypotheses hy
            (by simpa [sy, cpy] using hs) (by simpa [hr] using hflat)
        simpa [hr] using Or.inr hh.1
    have hsxFlat : ∀ t us, sx = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor → us = [] := by
      intro t us hs hflat
      apply hlhda_suffix_flat_forces_terminal hx hxne
        (by simpa [sx, cpx] using hs)
      rw [← hflat]
      exact hlhda_firstDir_mem_edgeVertices _ us
    have hsyFlat : ∀ t us, sy = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor → us = [] := by
      intro t us hs hflat
      apply hlhda_suffix_flat_forces_terminal hy hyne
        (by simpa [sy, cpy] using hs)
      rw [← hflat, hr]
      exact hlhda_firstDir_mem_edgeVertices _ us
    have hsuf : sx = sy := hlhda_forwardCode_injective r.dir hrIn
      hsxLegal hsyLegal hsxDir hsyDir hsxFlat hsyFlat hsufCode
    calc
      xs = px ++ sx := by
        simpa [px, sx, cpx] using (List.take_append_drop cpx xs).symm
      _ = py ++ sy := congrArg₂ List.append hpre hsuf
      _ = ys := by
        simpa [py, sy, cpy] using List.take_append_drop cpy ys




noncomputable def hlhda_decodePair (p : List ℤ × List ℤ) : List ℤ := by
  classical
  exact if h : ∃ ts : List ℤ, ∃ hleg :
      (ofTurns hexAWStart 1 ts).IsLegalSAW,
      hlhda_augmentedPair ts hleg = p then Classical.choose h else []

theorem hlhda_decodePair_augmented (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_decodePair (hlhda_augmentedPair ts hleg) = ts := by
  classical
  unfold hlhda_decodePair
  rw [dif_pos ⟨ts, hleg, rfl⟩]
  let h : ∃ us : List ℤ, ∃ hu :
      (ofTurns hexAWStart 1 us).IsLegalSAW,
      hlhda_augmentedPair us hu = hlhda_augmentedPair ts hleg :=
    ⟨ts, hleg, rfl⟩
  obtain ⟨hu, hp⟩ := Classical.choose_spec h
  exact hlhda_augmentedPair_injective hu hleg hp


end

end StatMech.Universality
