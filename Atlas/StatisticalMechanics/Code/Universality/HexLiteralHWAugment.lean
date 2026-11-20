/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexLiteralHWRecursive
import Code.Universality.HexHalfEdgeClose

namespace StatMech.Universality

open HexWalk



def hlha_negCoord (p : HexReturnCoord) : HexReturnCoord :=
  ⟨-p.x, -p.y⟩

def hlha_swapCoord (p : HexReturnCoord) : HexReturnCoord :=
  ⟨p.y, p.x⟩

@[simp] theorem hlha_negCoord_x (p : HexReturnCoord) :
    (hlha_negCoord p).x = -p.x := rfl

@[simp] theorem hlha_negCoord_y (p : HexReturnCoord) :
    (hlha_negCoord p).y = -p.y := rfl

@[simp] theorem hlha_swapCoord_x (p : HexReturnCoord) :
    (hlha_swapCoord p).x = p.y := rfl

@[simp] theorem hlha_swapCoord_y (p : HexReturnCoord) :
    (hlha_swapCoord p).y = p.x := rfl

@[simp] theorem hlha_negCoord_zero :
    hlha_negCoord HexReturnCoord.zero = HexReturnCoord.zero := rfl

@[simp] theorem hlha_swapCoord_zero :
    hlha_swapCoord HexReturnCoord.zero = HexReturnCoord.zero := rfl

theorem hlha_negCoord_injective : Function.Injective hlha_negCoord := by
  intro p q h
  cases p
  cases q
  simp only [hlha_negCoord, HexReturnCoord.mk.injEq] at h ⊢
  omega

theorem hlha_swapCoord_injective : Function.Injective hlha_swapCoord := by
  intro p q h
  cases p
  cases q
  simp only [hlha_swapCoord, HexReturnCoord.mk.injEq] at h ⊢
  exact ⟨h.2, h.1⟩

theorem hlha_add_left_injective (q : HexReturnCoord) :
    Function.Injective q.add := by
  intro p r h
  cases q
  cases p
  cases r
  simp only [HexReturnCoord.add, HexReturnCoord.mk.injEq] at h ⊢
  omega

@[simp] theorem hlha_add_zero (q : HexReturnCoord) :
    q.add HexReturnCoord.zero = q := by
  cases q
  simp [HexReturnCoord.add, HexReturnCoord.zero]

@[simp] theorem hlha_zero_add (q : HexReturnCoord) :
    HexReturnCoord.zero.add q = q := by
  cases q
  simp [HexReturnCoord.add, HexReturnCoord.zero]

@[simp] theorem hlha_negCoord_add (p q : HexReturnCoord) :
    hlha_negCoord (p.add q) =
      (hlha_negCoord p).add (hlha_negCoord q) := by
  cases p
  cases q
  simp [hlha_negCoord, HexReturnCoord.add]
  constructor <;> omega

@[simp] theorem hlha_swapCoord_add (p q : HexReturnCoord) :
    hlha_swapCoord (p.add q) =
      (hlha_swapCoord p).add (hlha_swapCoord q) := by
  cases p
  cases q
  simp [hlha_swapCoord, HexReturnCoord.add]

theorem hlha_negCoord_turn (d : HexReturnCoord) {t : ℤ}
    (ht : t = 1 ∨ t = -1) :
    hlha_negCoord (d.turn t) = (hlha_negCoord d).turn t := by
  rcases d with ⟨x, y⟩
  rcases ht with rfl | rfl <;>
    simp [hlha_negCoord, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] <;> omega

theorem hlha_swapCoord_turn (d : HexReturnCoord) {t : ℤ}
    (ht : t = 1 ∨ t = -1) :
    hlha_swapCoord (d.turn t) =
      (hlha_swapCoord d).turn (-t) := by
  rcases d with ⟨x, y⟩
  rcases ht with rfl | rfl <;>
    simp [hlha_swapCoord, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right]



def hlha_coordVertices (p d : HexReturnCoord) :
    List ℤ → List HexReturnCoord
  | [] => [p]
  | t :: ts =>
      p :: hlha_coordVertices (p.add (d.turn t)) (d.turn t) ts



def hlha_edgeVertices (p d : HexReturnCoord) :
    List ℤ → List HexReturnCoord
  | [] => [p, p.add d]
  | t :: ts =>
      p :: hlha_edgeVertices (p.add d) (d.turn t) ts

@[simp] theorem hlha_coordVertices_length (p d : HexReturnCoord)
    (ts : List ℤ) :
    (hlha_coordVertices p d ts).length = ts.length + 1 := by
  induction ts generalizing p d with
  | nil => rfl
  | cons t ts ih => simp [hlha_coordVertices, ih]

@[simp] theorem hlha_edgeVertices_length (p d : HexReturnCoord)
    (ts : List ℤ) :
    (hlha_edgeVertices p d ts).length = ts.length + 2 := by
  induction ts generalizing p d with
  | nil => rfl
  | cons t ts ih => simp [hlha_edgeVertices, ih]

theorem hlha_edgeVertices_start_mem (p d : HexReturnCoord) (ts : List ℤ) :
    p ∈ hlha_edgeVertices p d ts := by
  cases ts <;> simp [hlha_edgeVertices]

theorem hlha_coordVertices_cons_eq_edge (p d : HexReturnCoord)
    (t : ℤ) (ts : List ℤ) :
    hlha_coordVertices p d (t :: ts) =
      hlha_edgeVertices p (d.turn t) ts := by
  induction ts generalizing p d t with
  | nil => simp [hlha_coordVertices, hlha_edgeVertices]
  | cons u ts ih =>
      rw [hlha_coordVertices, hlha_edgeVertices, ih]

theorem hlha_coordVertices_neg (p d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_coordVertices (hlha_negCoord p) (hlha_negCoord d) ts =
      (hlha_coordVertices p d ts).map hlha_negCoord := by
  induction ts generalizing p d with
  | nil => simp [hlha_coordVertices]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simp only [hlha_coordVertices, List.map_cons]
      rw [← hlha_negCoord_turn d ht, ← hlha_negCoord_add]
      exact congrArg (List.cons (hlha_negCoord p))
        (ih (p.add (d.turn t)) (d.turn t) htail)

theorem hlha_edgeVertices_neg (p d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_edgeVertices (hlha_negCoord p) (hlha_negCoord d) ts =
      (hlha_edgeVertices p d ts).map hlha_negCoord := by
  induction ts generalizing p d with
  | nil => simp [hlha_edgeVertices]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simp only [hlha_edgeVertices, List.map_cons]
      rw [← hlha_negCoord_add, ← hlha_negCoord_turn d ht]
      exact congrArg (List.cons (hlha_negCoord p))
        (ih (p.add d) (d.turn t) htail)

theorem hlha_edgeVertices_swap (p d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_edgeVertices (hlha_swapCoord p) (hlha_swapCoord d)
        (hsc_negTurns ts) =
      (hlha_edgeVertices p d ts).map hlha_swapCoord := by
  induction ts generalizing p d with
  | nil => simp [hlha_edgeVertices]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      rw [hsc_negTurns_cons]
      simp only [hlha_edgeVertices, List.map_cons]
      rw [← hlha_swapCoord_add, ← hlha_swapCoord_turn d ht]
      exact congrArg (List.cons (hlha_swapCoord p))
        (ih (p.add d) (d.turn t) htail)

theorem hlha_edgeVertices_translate (q p d : HexReturnCoord)
    (ts : List ℤ) :
    hlha_edgeVertices (q.add p) d ts =
      (hlha_edgeVertices p d ts).map (fun r => q.add r) := by
  induction ts generalizing p d with
  | nil =>
      simp [hlha_edgeVertices, HexReturnCoord.add]
      cases q
      cases p
      cases d
      simp
      constructor <;> omega
  | cons t ts ih =>
      simp only [hlha_edgeVertices, List.map_cons]
      rw [show (q.add p).add d = q.add (p.add d) by
        cases q
        cases p
        cases d
        simp [HexReturnCoord.add]
        constructor <;> omega]
      exact congrArg (List.cons (q.add p)) (ih (p.add d) (d.turn t))




def HLHAAwayDir (d : HexReturnCoord) : Prop :=
  d = ⟨1, 1⟩ ∨ d = ⟨0, 1⟩ ∨ d = ⟨-1, 0⟩ ∨ d = ⟨-1, -1⟩



def hlha_useSwap (d : HexReturnCoord) : Bool :=
  decide (d = ⟨0, 1⟩ ∨ d = ⟨-1, -1⟩)



def hlha_cutTurn (d : HexReturnCoord) : ℤ :=
  if d = ⟨0, 1⟩ ∨ d = ⟨-1, 0⟩ then 1 else -1

def hlha_normCoord (d p : HexReturnCoord) : HexReturnCoord :=
  if hlha_useSwap d then hlha_swapCoord p else hlha_negCoord p

def hlha_normTurns (d : HexReturnCoord) (ts : List ℤ) : List ℤ :=
  if hlha_useSwap d then hsc_negTurns ts else ts


def hlha_augmentSide (d : HexReturnCoord) (internal : List ℤ) : List ℤ :=
  -1 :: hlha_cutTurn d :: hlha_normTurns d internal

def hlha_outerStep : HexReturnCoord :=
  HexReturnCoord.base.turn (-1)

@[simp] theorem hlha_outerStep_eq : hlha_outerStep = ⟨0, -1⟩ := by
  simp [hlha_outerStep, HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.right]

@[simp] theorem hlha_coordHeight_zero :
    HexReturnCoord.zero.x - HexReturnCoord.zero.y = 0 := rfl

@[simp] theorem hlha_outerStep_height :
    hlha_outerStep.x - hlha_outerStep.y = 1 := by
  rw [hlha_outerStep_eq]
  rfl

theorem hlha_normCoord_height (d p : HexReturnCoord) :
    (hlha_normCoord d p).x - (hlha_normCoord d p).y =
      -(p.x - p.y) := by
  unfold hlha_normCoord
  split <;> simp <;> omega

theorem hlha_normCoord_injective (d : HexReturnCoord) :
    Function.Injective (hlha_normCoord d) := by
  unfold hlha_normCoord
  split
  · exact hlha_swapCoord_injective
  · exact hlha_negCoord_injective

theorem hlha_normDir_eq (d : HexReturnCoord) (hd : HLHAAwayDir d) :
    hlha_normCoord d d =
      hlha_outerStep.turn (hlha_cutTurn d) := by
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [hlha_normCoord, hlha_useSwap, hlha_cutTurn, hlha_outerStep,
      HexReturnCoord.base, HexReturnCoord.turn, HexReturnCoord.left,
      HexReturnCoord.right, hlha_swapCoord, hlha_negCoord]

theorem hlha_normTurns_legal (d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∀ t ∈ hlha_normTurns d ts, t = 1 ∨ t = -1 := by
  unfold hlha_normTurns
  split
  · intro t ht
    unfold hsc_negTurns at ht
    rw [List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    rcases hlegal u hu with rfl | rfl <;> simp
  · exact hlegal

theorem hlha_augmentSide_legal (d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∀ t ∈ hlha_augmentSide d ts, t = 1 ∨ t = -1 := by
  intro t ht
  simp only [hlha_augmentSide, List.mem_cons] at ht
  rcases ht with rfl | rfl | ht
  · exact Or.inr rfl
  · unfold hlha_cutTurn
    split <;> simp
  · exact hlha_normTurns_legal d ts hlegal t ht

@[simp] theorem hlha_augmentSide_length (d : HexReturnCoord)
    (ts : List ℤ) :
    (hlha_augmentSide d ts).length = ts.length + 2 := by
  unfold hlha_augmentSide hlha_normTurns
  split <;> simp [hsc_negTurns]

theorem hlha_normEdgeVertices (d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_edgeVertices hlha_outerStep (hlha_normCoord d d)
        (hlha_normTurns d ts) =
      (hlha_edgeVertices HexReturnCoord.zero d ts).map
        (fun p => hlha_outerStep.add (hlha_normCoord d p)) := by
  unfold hlha_normTurns hlha_normCoord
  split <;> rename_i hswap
  · have htrans := hlha_edgeVertices_translate hlha_outerStep
        HexReturnCoord.zero (hlha_swapCoord d) (hsc_negTurns ts)
    have hswapv := hlha_edgeVertices_swap HexReturnCoord.zero d ts hlegal
    simp only [hlha_add_zero, hlha_swapCoord_zero] at htrans hswapv
    rw [htrans, hswapv, List.map_map]
    rfl
  · have htrans := hlha_edgeVertices_translate hlha_outerStep
        HexReturnCoord.zero (hlha_negCoord d) ts
    have hnegv := hlha_edgeVertices_neg HexReturnCoord.zero d ts hlegal
    simp only [hlha_add_zero, hlha_negCoord_zero] at htrans hnegv
    rw [htrans, hnegv, List.map_map]
    rfl

theorem hlha_coordVertices_augmentSide (d : HexReturnCoord) (ts : List ℤ)
    (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (hlha_augmentSide d ts) =
      HexReturnCoord.zero ::
        (hlha_edgeVertices HexReturnCoord.zero d ts).map
          (fun p => hlha_outerStep.add (hlha_normCoord d p)) := by
  rw [show hlha_augmentSide d ts =
      (-1 : ℤ) :: hlha_cutTurn d :: hlha_normTurns d ts from rfl]
  rw [hlha_coordVertices_cons_eq_edge]
  simp only [hlha_edgeVertices]
  change HexReturnCoord.zero ::
      hlha_edgeVertices hlha_outerStep
        (hlha_outerStep.turn (hlha_cutTurn d)) (hlha_normTurns d ts) = _
  rw [← hlha_normDir_eq d hd, hlha_normEdgeVertices d ts hlegal]



theorem hlha_augmented_vertex_height_pos (d p : HexReturnCoord)
    (hp : p.x - p.y ≤ 0) :
    0 < (hlha_outerStep.add (hlha_normCoord d p)).x -
      (hlha_outerStep.add (hlha_normCoord d p)).y := by
  have ho := hlha_outerStep_height
  have hn := hlha_normCoord_height d p
  simp only [HexReturnCoord.add]
  omega



theorem hlha_coordVertices_augmentSide_nodup (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d ts).Nodup)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
      (hlha_augmentSide d ts)).Nodup := by
  rw [hlha_coordVertices_augmentSide d ts hd hlegal]
  rw [List.nodup_cons]
  constructor
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, hp, heq⟩ := hmem
    have hpos := hlha_augmented_vertex_height_pos d p (hbehind p hp)
    rw [heq] at hpos
    simp [HexReturnCoord.zero] at hpos
  · apply hnodup.map
    intro p q heq
    apply hlha_normCoord_injective d
    exact hlha_add_left_injective hlha_outerStep heq





noncomputable def hlha_realizeCoord (m s : ℂ) (h : ℤ)
    (p r : HexReturnCoord) : ℂ :=
  m + halfStep h + 2 * ((r.value - p.value) * s)


theorem hlha_verticesAux_coord (p d : HexReturnCoord) (m s : ℂ)
    (h : ℤ) (ts : List ℤ)
    (hdir : halfStep h = d.value * s)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    verticesAux m h ts =
      (hlha_coordVertices p d ts).map (hlha_realizeCoord m s h p) := by
  induction ts generalizing p d m h with
  | nil =>
      simp [verticesAux, hlha_coordVertices, hlha_realizeCoord]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : halfStep (h + t) = e.value * s :=
        hexReturn_halfStep_turn s h d t hdir ht
      rw [verticesAux_cons, hlha_coordVertices, List.map_cons]
      congr 1
      · simp [hlha_realizeCoord]
      · rw [ih (p.add e) e
          (m + halfStep h + halfStep (h + t)) (h + t) he htail]
        apply List.map_congr_left
        intro r _
        unfold hlha_realizeCoord
        rw [he, HexReturnCoord.value_add]
        ring

noncomputable def hlha_standardRealize (p : HexReturnCoord) : ℂ :=
  halfStep 0 + 2 * (p.value * halfStep 0)



theorem hlha_standard_vertices (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) :
    (ofTurns 0 0 ts).vertices =
      (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).map
        hlha_standardRealize := by
  have hdir : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have h := hlha_verticesAux_coord HexReturnCoord.zero HexReturnCoord.base
    0 (halfStep 0) 0 ts hdir hlegal
  change verticesAux 0 0 ts = _
  rw [h]
  apply List.map_congr_left
  intro p _
  simp [hlha_realizeCoord, hlha_standardRealize,
    HexReturnCoord.value_zero]

theorem hlha_value_injective :
    Function.Injective HexReturnCoord.value := by
  intro p q h
  have hz : (((p.x - q.x : ℤ) : ℝ) : ℂ) +
      (((p.y - q.y : ℤ) : ℝ) : ℂ) * hexOmega = 0 := by
    unfold HexReturnCoord.value at h
    push_cast
    linear_combination h
  obtain ⟨hx, hy⟩ := hexConcrete_omega_lin_indep
    ((p.x - q.x : ℤ) : ℝ) ((p.y - q.y : ℤ) : ℝ) hz
  have hx0 : p.x - q.x = 0 := by exact_mod_cast hx
  have hy0 : p.y - q.y = 0 := by exact_mod_cast hy
  have hx' : p.x = q.x := sub_eq_zero.mp hx0
  have hy' : p.y = q.y := sub_eq_zero.mp hy0
  cases p
  cases q
  simp_all

theorem hlha_standardRealize_injective :
    Function.Injective hlha_standardRealize := by
  intro p q h
  apply hlha_value_injective
  have hstep : halfStep 0 ≠ 0 := hexConcrete_halfStep_ne 0
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  unfold hlha_standardRealize at h
  have hm : (p.value - q.value) * halfStep 0 = 0 := by
    apply (mul_left_cancel₀ htwo)
    linear_combination h
  rcases mul_eq_zero.mp hm with hpq | hs
  · exact sub_eq_zero.mp hpq
  · exact (hstep hs).elim


theorem hlha_standard_isSAW_iff (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) :
    (ofTurns 0 0 ts).IsSAW ↔
      (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).Nodup := by
  rw [IsSAW, hlha_standard_vertices ts hlegal,
    List.nodup_map_iff hlha_standardRealize_injective]



theorem hlha_coordRun_take_mem_tail (p d : HexReturnCoord) (ts : List ℤ)
    {k : ℕ} (hk : 0 < k) (hkle : k ≤ ts.length) :
    (hlhr_coordRun p d (ts.take k)).pos ∈
      (hlha_coordVertices p d ts).tail := by
  induction ts generalizing p d k with
  | nil =>
      simp only [List.length_nil] at hkle
      omega
  | cons t ts ih =>
      cases k with
      | zero => omega
      | succ j =>
          simp only [List.take_succ_cons, hlhr_coordRun,
            hlha_coordVertices, List.tail_cons]
          cases j with
          | zero =>
              have hstart : p.add (d.turn t) ∈
                  hlha_coordVertices (p.add (d.turn t)) (d.turn t) ts := by
                cases ts <;> simp [hlha_coordVertices]
              simpa [hlhr_coordRun] using hstart
          | succ j =>
              apply List.mem_of_mem_tail
              exact ih (p.add (d.turn t)) (d.turn t) (k := j + 1)
                (by omega) (by
                  simp only [List.length_cons] at hkle
                  omega)



theorem hlha_augmentSide_latticeHeight_pos (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) {k : ℕ} (hk : 0 < k)
    (hkle : k ≤ (hlha_augmentSide d ts).length) :
    0 < hlhr_latticeHeight (hlha_augmentSide d ts) k := by
  have hmem := hlha_coordRun_take_mem_tail HexReturnCoord.zero
    HexReturnCoord.base (hlha_augmentSide d ts) hk hkle
  rw [hlha_coordVertices_augmentSide d ts hd hlegal] at hmem
  simp only [List.tail_cons, List.mem_map] at hmem
  obtain ⟨p, hp, heq⟩ := hmem
  have hpos := hlha_augmented_vertex_height_pos d p (hbehind p hp)
  unfold hlhr_latticeHeight
  change 0 <
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
      ((hlha_augmentSide d ts).take k)).pos.x -
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
      ((hlha_augmentSide d ts).take k)).pos.y
  rw [← heq]
  exact hpos


theorem hlha_augmentSide_halfSpace (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) :
    HLHRLiteralHalfSpace 0 (hlha_augmentSide d ts) := by
  intro k hk hkle
  have hturns : (ofTurns 0 0 (hlha_augmentSide d ts)).LegalTurns :=
    hlha_augmentSide_legal d ts hlegal
  rw [hlhr_height_eq_latticeHeight _ hturns 0,
    hlhr_height_eq_latticeHeight _ hturns k]
  have hkpos := hlha_augmentSide_latticeHeight_pos d ts hd hlegal
    hbehind hk hkle
  have hzero : hlhr_latticeHeight (hlha_augmentSide d ts) 0 = 0 := rfl
  rw [hzero]
  norm_num
  exact hkpos


theorem hlha_augmentSide_isLegalSAW (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d ts).Nodup)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) :
    (ofTurns 0 0 (hlha_augmentSide d ts)).IsLegalSAW := by
  have hturns : (ofTurns 0 0 (hlha_augmentSide d ts)).LegalTurns :=
    hlha_augmentSide_legal d ts hlegal
  refine ⟨hturns, ?_⟩
  rw [hlha_standard_isSAW_iff _ hturns]
  exact hlha_coordVertices_augmentSide_nodup d ts hd hlegal hnodup hbehind



theorem hlha_coordRun_direction_isUnit (p d : HexReturnCoord)
    (ts : List ℤ) (hd : d.IsUnit)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hlhr_coordRun p d ts).dir.IsUnit := by
  induction ts generalizing p d with
  | nil => simpa [hlhr_coordRun] using hd
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simpa [hlhr_coordRun] using
        ih (p.add (d.turn t)) (d.turn t) (d.isUnit_turn hd ht) htail



theorem hlha_mem_coordVertices (p d : HexReturnCoord) (ts : List ℤ)
    {q : HexReturnCoord} (hq : q ∈ hlha_coordVertices p d ts) :
    ∃ k, k ≤ ts.length ∧ q = (hlhr_coordRun p d (ts.take k)).pos := by
  induction ts generalizing p d q with
  | nil =>
      simp [hlha_coordVertices] at hq
      subst q
      exact ⟨0, by simp, by simp [hlhr_coordRun]⟩
  | cons t ts ih =>
      simp only [hlha_coordVertices, List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        exact ⟨0, by simp, by simp [hlhr_coordRun]⟩
      · obtain ⟨k, hk, heq⟩ :=
          ih (p.add (d.turn t)) (d.turn t) (q := q) hq
        refine ⟨k + 1, by simp; omega, ?_⟩
        simp only [List.take_succ_cons, hlhr_coordRun]
        exact heq



theorem hlha_coordVertices_drop (p d : HexReturnCoord) (ts : List ℤ)
    (cp : ℕ) (hcp : cp ≤ ts.length) :
    let r := hlhr_coordRun p d (ts.take cp)
    hlha_coordVertices r.pos r.dir (ts.drop cp) =
      (hlha_coordVertices p d ts).drop cp := by
  induction ts generalizing p d cp with
  | nil =>
      have : cp = 0 := by simpa using hcp
      subst cp
      simp [hlhr_coordRun, hlha_coordVertices]
  | cons t ts ih =>
      cases cp with
      | zero => simp [hlhr_coordRun, hlha_coordVertices]
      | succ cp =>
          simp only [List.take_succ_cons, List.drop_succ_cons, hlhr_coordRun,
            hlha_coordVertices, List.drop_succ_cons]
          apply ih
          simp only [List.length_cons] at hcp
          omega



theorem hlha_cut_latticeHeight_max (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (k : ℕ)
    (hk : k ≤ ts.length) :
    hlhr_latticeHeight ts k ≤
      hlhr_latticeHeight ts (hexW2_cutPos 0 ts) := by
  have hmax := hexW2_cutPos_max 0 ts k hk
  change hlhr_height 0 ts k ≤
    hlhr_height 0 ts (hexW2_cutPos 0 ts) at hmax
  rw [hlhr_height_eq_latticeHeight ts hlegal k,
    hlhr_height_eq_latticeHeight ts hlegal (hexW2_cutPos 0 ts)] at hmax
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  have hcast : (hlhr_latticeHeight ts k : ℝ) ≤
      (hlhr_latticeHeight ts (hexW2_cutPos 0 ts) : ℝ) := by
    nlinarith
  exact_mod_cast hcast



theorem hlha_source_standard_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns 0 0 ts).IsLegalSAW :=
  (hhe_isLegalSAW_rebase a 0 h0 0 ts).mpr hlegal


theorem hlha_source_coord_nodup (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).Nodup := by
  have hs := hlha_source_standard_legal a h0 ts hlegal
  exact (hlha_standard_isSAW_iff ts hs.1).mp hs.2



theorem hlha_awayDir_of_isUnit_of_height_nonpos (d : HexReturnCoord)
    (hu : d.IsUnit) (hh : d.x - d.y ≤ 0) : HLHAAwayDir d := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HLHAAwayDir] at hh ⊢



def hlha_emptyAugment : List ℤ := [-1]

theorem hlha_emptyAugment_isLegalSAW :
    (ofTurns 0 0 hlha_emptyAugment).IsLegalSAW := by
  simpa [hlha_emptyAugment] using hexWall3_isLegalSAW_witness (0 : ℂ)

theorem hlha_emptyAugment_halfSpace :
    HLHRLiteralHalfSpace 0 hlha_emptyAugment := by
  intro k hk hkle
  have hk1 : k = 1 := by
    simp only [hlha_emptyAugment, List.length_singleton] at hkle
    omega
  subst k
  have hturns := hlha_emptyAugment_isLegalSAW.1
  rw [hlhr_height_eq_latticeHeight _ hturns 0,
    hlhr_height_eq_latticeHeight _ hturns 1]
  norm_num [hlhr_latticeHeight, hlha_emptyAugment, hlhr_coordRun,
    HexReturnCoord.base, HexReturnCoord.turn, HexReturnCoord.right,
    HexReturnCoord.add, HexReturnCoord.zero]

@[simp] theorem hlha_emptyAugment_length : hlha_emptyAugment.length = 1 := rfl

noncomputable def hlha_cutState (ts : List ℤ) : HLHRCoordRun :=
  hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
    (ts.take (hexW2_cutPos 0 ts))

noncomputable def hlha_suffixAugment (ts : List ℤ) : List ℤ :=
  match ts.drop (hexW2_cutPos 0 ts) with
  | [] => hlha_emptyAugment
  | t :: us => hlha_augmentSide ((hlha_cutState ts).dir.turn t) us

theorem hlha_suffix_side_hypotheses (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hsource : (ofTurns a h0 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuffix : ts.drop (hexW2_cutPos 0 ts) = t :: us) :
    let d := (hlha_cutState ts).dir.turn t
    HLHAAwayDir d ∧
      (∀ u ∈ us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d us).Nodup ∧
      ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d us,
        p.x - p.y ≤ 0 := by
  have hstd := hlha_source_standard_legal a h0 ts hsource
  have hcple := hexW2_cutPos_le 0 ts
  let r := hlha_cutState ts
  let d := r.dir.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_drop
    rw [hsuffix]
    simp
  have ht := hstd.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hudrop : u ∈ ts.drop (hexW2_cutPos 0 ts) := by
      rw [hsuffix]
      simp [hu]
    exact hstd.1 u (List.mem_of_mem_drop hudrop)
  have habs :
      hlha_edgeVertices r.pos d us =
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).drop
          (hexW2_cutPos 0 ts) := by
    have hdrop := hlha_coordVertices_drop HexReturnCoord.zero
      HexReturnCoord.base ts (hexW2_cutPos 0 ts) hcple
    rw [hsuffix] at hdrop
    change hlha_coordVertices r.pos r.dir (t :: us) = _ at hdrop
    rw [hlha_coordVertices_cons_eq_edge] at hdrop
    exact hdrop
  have htrans :
      hlha_edgeVertices r.pos d us =
        (hlha_edgeVertices HexReturnCoord.zero d us).map r.pos.add := by
    simpa [hlha_add_zero] using
      hlha_edgeVertices_translate r.pos HexReturnCoord.zero d us
  have hfullnd := hlha_source_coord_nodup a h0 ts hsource
  have habsnd : (hlha_edgeVertices r.pos d us).Nodup := by
    rw [habs]
    exact hfullnd.drop
  have hrelnd : (hlha_edgeVertices HexReturnCoord.zero d us).Nodup := by
    rw [htrans] at habsnd
    exact habsnd.of_map
  have hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d us,
      p.x - p.y ≤ 0 := by
    intro p hp
    have habsmem : r.pos.add p ∈ hlha_edgeVertices r.pos d us := by
      rw [htrans, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hdropmem : r.pos.add p ∈
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).drop
          (hexW2_cutPos 0 ts) := by
      rw [← habs]
      exact habsmem
    have hfullmem : r.pos.add p ∈
        hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts :=
      List.mem_of_mem_drop hdropmem
    obtain ⟨k, hk, heq⟩ := hlha_mem_coordVertices
      HexReturnCoord.zero HexReturnCoord.base ts hfullmem
    have hmax := hlha_cut_latticeHeight_max ts hstd.1 k hk
    have hrheight : r.pos.x - r.pos.y =
        hlhr_latticeHeight ts (hexW2_cutPos 0 ts) := by
      rfl
    have hpheight : (r.pos.add p).x - (r.pos.add p).y =
        hlhr_latticeHeight ts k := by
      rw [heq]
      rfl
    simp only [HexReturnCoord.add] at hpheight
    omega
  have hrunit : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base (ts.take (hexW2_cutPos 0 ts))
      HexReturnCoord.base_isUnit
    intro u hu
    exact hstd.1 u (List.mem_of_mem_take hu)
  have hdunit : d.IsUnit := r.dir.isUnit_turn hrunit ht
  have hdmem : d ∈ hlha_edgeVertices HexReturnCoord.zero d us := by
    cases us with
    | nil => simp [hlha_edgeVertices]
    | cons u us =>
        simp only [hlha_edgeVertices, List.mem_cons]
        right
        simpa using hlha_edgeVertices_start_mem d (d.turn u) us
  have hdheight := hbehind d hdmem
  exact ⟨hlha_awayDir_of_isUnit_of_height_nonpos d hdunit hdheight,
    hus, hrelnd, hbehind⟩



theorem hlha_suffixAugment_spec (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns 0 0 (hlha_suffixAugment ts)).IsLegalSAW ∧
      HLHRLiteralHalfSpace 0 (hlha_suffixAugment ts) ∧
      (hlha_suffixAugment ts).length =
        (ts.drop (hexW2_cutPos 0 ts)).length + 1 := by
  unfold hlha_suffixAugment
  generalize hs : ts.drop (hexW2_cutPos 0 ts) = suffix
  cases suffix with
  | nil =>
      simp only
      refine ⟨hlha_emptyAugment_isLegalSAW,
        hlha_emptyAugment_halfSpace, ?_⟩
      simp [hlha_emptyAugment]
  | cons t us =>
      obtain ⟨hd, hlegal, hnodup, hbehind⟩ :=
        hlha_suffix_side_hypotheses a h0 ts hsource hs
      refine ⟨hlha_augmentSide_isLegalSAW _ _ hd hlegal hnodup hbehind,
        hlha_augmentSide_halfSpace _ _ hd hlegal hbehind, ?_⟩
      rw [hlha_augmentSide_length]
      simp



@[simp] theorem hlha_negCoord_negCoord (p : HexReturnCoord) :
    hlha_negCoord (hlha_negCoord p) = p := by
  cases p
  simp [hlha_negCoord]

@[simp] theorem hlha_add_neg_self (p : HexReturnCoord) :
    p.add (hlha_negCoord p) = HexReturnCoord.zero := by
  cases p
  simp [HexReturnCoord.add, HexReturnCoord.zero, hlha_negCoord]

@[simp] theorem hlha_add_neg_cancel_left (p q : HexReturnCoord) :
    (p.add q).add (hlha_negCoord q) = p := by
  cases p
  cases q
  simp [HexReturnCoord.add, hlha_negCoord]

theorem hlha_negTurn_back (d : HexReturnCoord) {t : ℤ}
    (ht : t = 1 ∨ t = -1) :
    (hlha_negCoord (d.turn t)).turn (-t) = hlha_negCoord d := by
  rcases d with ⟨x, y⟩
  rcases ht with rfl | rfl <;>
    simp [hlha_negCoord, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] <;> omega

@[simp] theorem hlha_loopReverse_cons (t : ℤ) (ts : List ℤ) :
    loopReverse (t :: ts) = loopReverse ts ++ [-t] := by
  simp [loopReverse]

theorem hlha_coordRun_append (p d : HexReturnCoord) (xs ys : List ℤ) :
    hlhr_coordRun p d (xs ++ ys) =
      let r := hlhr_coordRun p d xs
      hlhr_coordRun r.pos r.dir ys := by
  induction xs generalizing p d with
  | nil => simp [hlhr_coordRun]
  | cons t xs ih =>
      simp only [List.cons_append, hlhr_coordRun]
      exact ih (p.add (d.turn t)) (d.turn t)



theorem hlha_edgeVertices_append_single (p d : HexReturnCoord)
    (ts : List ℤ) (t : ℤ) :
    let r := hlhr_coordRun (p.add d) d ts
    hlha_edgeVertices p d (ts ++ [t]) =
      hlha_edgeVertices p d ts ++ [r.pos.add (r.dir.turn t)] := by
  induction ts generalizing p d with
  | nil =>
      simp [hlha_edgeVertices, hlhr_coordRun]
  | cons u ts ih =>
      simp only [List.cons_append, hlha_edgeVertices, hlhr_coordRun,
        List.cons_append]
      rw [ih (p.add d) (d.turn u)]



theorem hlha_edgeVertices_loopReverse (p d : HexReturnCoord)
    (ts : List ℤ) (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hlhr_coordRun (p.add d) d ts
    hlha_edgeVertices r.pos (hlha_negCoord r.dir) (loopReverse ts) =
        (hlha_edgeVertices p d ts).reverse ∧
      hlhr_coordRun (r.pos.add (hlha_negCoord r.dir))
          (hlha_negCoord r.dir) (loopReverse ts) =
        ⟨p, hlha_negCoord d⟩ := by
  induction ts generalizing p d with
  | nil =>
      simp [hlhr_coordRun, hlha_edgeVertices, loopReverse]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      let r := hlhr_coordRun ((p.add d).add e) e ts
      have hih := ih (p.add d) e htail
      change
        hlha_edgeVertices r.pos (hlha_negCoord r.dir)
            (loopReverse (t :: ts)) =
            (hlha_edgeVertices p d (t :: ts)).reverse ∧
          hlhr_coordRun (r.pos.add (hlha_negCoord r.dir))
              (hlha_negCoord r.dir) (loopReverse (t :: ts)) =
            ⟨p, hlha_negCoord d⟩
      rw [hlha_loopReverse_cons]
      constructor
      · rw [hlha_edgeVertices_append_single]
        rw [hih.1]
        simp only [hlha_edgeVertices, List.reverse_cons]
        rw [hih.2]
        simp only
        rw [hlha_negTurn_back d ht, hlha_add_neg_cancel_left]
      · rw [hlha_coordRun_append]
        rw [hih.2]
        simp only [hlhr_coordRun]
        rw [hlha_negTurn_back d ht, hlha_add_neg_cancel_left]


noncomputable def hlha_prefixReverseData (ts : List ℤ) :
    Option (HexReturnCoord × List ℤ) :=
  match ts.take (hexW2_cutPos 0 ts) with
  | [] => none
  | _ :: us =>
      let r := hlha_cutState ts
      some (hlha_negCoord r.dir, loopReverse us)

noncomputable def hlha_prefixAugment (ts : List ℤ) : List ℤ :=
  match hlha_prefixReverseData ts with
  | none => hlha_emptyAugment
  | some (d, us) => hlha_augmentSide d us

theorem hlha_negCoord_isUnit {d : HexReturnCoord} (hd : d.IsUnit) :
    (hlha_negCoord d).IsUnit := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HexReturnCoord.IsUnit, hlha_negCoord]

theorem hlha_coordVertices_take (p d : HexReturnCoord) (ts : List ℤ)
    (cp : ℕ) :
    hlha_coordVertices p d (ts.take cp) =
      (hlha_coordVertices p d ts).take (cp + 1) := by
  induction ts generalizing p d cp with
  | nil =>
      cases cp <;> simp [hlha_coordVertices]
  | cons t ts ih =>
      cases cp with
      | zero => simp [hlha_coordVertices]
      | succ cp =>
          rw [List.take_succ_cons, hlha_coordVertices, hlha_coordVertices,
            List.take_succ_cons, ih]

theorem hlha_prefix_side_hypotheses (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hsource : (ofTurns a h0 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hprefix : ts.take (hexW2_cutPos 0 ts) = t :: us) :
    let d := hlha_negCoord (hlha_cutState ts).dir
    HLHAAwayDir d ∧
      (∀ u ∈ loopReverse us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup ∧
      ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d (loopReverse us),
        p.x - p.y ≤ 0 := by
  have hstd := hlha_source_standard_legal a h0 ts hsource
  have hcple := hexW2_cutPos_le 0 ts
  let r := hlha_cutState ts
  let d0 := HexReturnCoord.base.turn t
  let d := hlha_negCoord r.dir
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_take
    rw [hprefix]
    simp
  have ht := hstd.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hutake : u ∈ ts.take (hexW2_cutPos 0 ts) := by
      rw [hprefix]
      simp [hu]
    exact hstd.1 u (List.mem_of_mem_take hutake)
  have hrevlegal : ∀ u ∈ loopReverse us, u = 1 ∨ u = -1 :=
    loopReverse_legal us hus
  have hrstate : hlhr_coordRun (HexReturnCoord.zero.add d0) d0 us = r := by
    dsimp [r, hlha_cutState, d0]
    rw [hprefix]
    simp only [hlhr_coordRun]
  have hrev := hlha_edgeVertices_loopReverse HexReturnCoord.zero d0 us hus
  rw [hrstate] at hrev
  have hprefixCoords :
      hlha_edgeVertices HexReturnCoord.zero d0 us =
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
          (hexW2_cutPos 0 ts + 1) := by
    rw [← hlha_coordVertices_take]
    rw [hprefix, hlha_coordVertices_cons_eq_edge]
  have habs :
      hlha_edgeVertices r.pos d (loopReverse us) =
        ((hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
          (hexW2_cutPos 0 ts + 1)).reverse := by
    dsimp [d]
    rw [hrev.1, hprefixCoords]
  have htrans :
      hlha_edgeVertices r.pos d (loopReverse us) =
        (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).map
          r.pos.add := by
    simpa using hlha_edgeVertices_translate r.pos HexReturnCoord.zero d
      (loopReverse us)
  have hfullnd := hlha_source_coord_nodup a h0 ts hsource
  have habsnd : (hlha_edgeVertices r.pos d (loopReverse us)).Nodup := by
    rw [habs]
    exact List.nodup_reverse.mpr hfullnd.take
  have hrelnd :
      (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup := by
    rw [htrans] at habsnd
    exact habsnd.of_map
  have hbehind : ∀ p ∈
      hlha_edgeVertices HexReturnCoord.zero d (loopReverse us),
      p.x - p.y ≤ 0 := by
    intro p hp
    have habsmem : r.pos.add p ∈
        hlha_edgeVertices r.pos d (loopReverse us) := by
      rw [htrans, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hprevmem : r.pos.add p ∈
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
          (hexW2_cutPos 0 ts + 1) := by
      have : r.pos.add p ∈
          ((hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
            (hexW2_cutPos 0 ts + 1)).reverse := by
        rw [← habs]
        exact habsmem
      exact List.mem_reverse.mp this
    have hfullmem : r.pos.add p ∈
        hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts :=
      List.mem_of_mem_take hprevmem
    obtain ⟨k, hk, heq⟩ := hlha_mem_coordVertices
      HexReturnCoord.zero HexReturnCoord.base ts hfullmem
    have hmax := hlha_cut_latticeHeight_max ts hstd.1 k hk
    have hrheight : r.pos.x - r.pos.y =
        hlhr_latticeHeight ts (hexW2_cutPos 0 ts) := by
      rfl
    have hpheight : (r.pos.add p).x - (r.pos.add p).y =
        hlhr_latticeHeight ts k := by
      rw [heq]
      rfl
    simp only [HexReturnCoord.add] at hpheight
    omega
  have hrunit : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base (ts.take (hexW2_cutPos 0 ts))
      HexReturnCoord.base_isUnit
    intro u hu
    exact hstd.1 u (List.mem_of_mem_take hu)
  have hdunit : d.IsUnit := hlha_negCoord_isUnit hrunit
  have hdmem : d ∈
      hlha_edgeVertices HexReturnCoord.zero d (loopReverse us) := by
    cases loopReverse us with
    | nil => simp [hlha_edgeVertices]
    | cons u vs =>
        simp only [hlha_edgeVertices, List.mem_cons]
        right
        simpa using hlha_edgeVertices_start_mem d (d.turn u) vs
  have hdheight := hbehind d hdmem
  exact ⟨hlha_awayDir_of_isUnit_of_height_nonpos d hdunit hdheight,
    hrevlegal, hrelnd, hbehind⟩



theorem hlha_prefixAugment_spec (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns 0 0 (hlha_prefixAugment ts)).IsLegalSAW ∧
      HLHRLiteralHalfSpace 0 (hlha_prefixAugment ts) ∧
      (hlha_prefixAugment ts).length =
        (ts.take (hexW2_cutPos 0 ts)).length + 1 := by
  unfold hlha_prefixAugment hlha_prefixReverseData
  generalize hp : ts.take (hexW2_cutPos 0 ts) = pre
  cases pre with
  | nil =>
      simp only
      refine ⟨hlha_emptyAugment_isLegalSAW,
        hlha_emptyAugment_halfSpace, ?_⟩
      simp [hlha_emptyAugment]
  | cons t us =>
      obtain ⟨hd, hlegal, hnodup, hbehind⟩ :=
        hlha_prefix_side_hypotheses a h0 ts hsource hp
      refine ⟨hlha_augmentSide_isLegalSAW _ _ hd hlegal hnodup hbehind,
        hlha_augmentSide_halfSpace _ _ hd hlegal hbehind, ?_⟩
      rw [hlha_augmentSide_length, loopReverse_length]
      simp



theorem hlha_halfStep_coord_neg_two :
    halfStep (-2) = (⟨-1, -1⟩ : HexReturnCoord).value * halfStep 0 := by
  have h0 : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hm1 := hexReturn_halfStep_turn (halfStep 0) 0
    HexReturnCoord.base (-1) h0 (Or.inr rfl)
  have hm2 := hexReturn_halfStep_turn (halfStep 0) (-1)
    (HexReturnCoord.base.turn (-1)) (-1) hm1 (Or.inr rfl)
  simpa [HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.right] using hm2

theorem hlha_halfStep_coord_neg_one :
    halfStep (-1) = (⟨0, -1⟩ : HexReturnCoord).value * halfStep 0 := by
  have h0 : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hm1 := hexReturn_halfStep_turn (halfStep 0) 0
    HexReturnCoord.base (-1) h0 (Or.inr rfl)
  simpa [HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.right] using hm1

theorem hlha_halfStep_coord_zero :
    halfStep 0 = (⟨1, 0⟩ : HexReturnCoord).value * halfStep 0 := by
  simp [HexReturnCoord.value]

theorem hlha_halfStep_coord_one :
    halfStep 1 = (⟨1, 1⟩ : HexReturnCoord).value * halfStep 0 := by
  have h0 : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have h1 := hexReturn_halfStep_turn (halfStep 0) 0
    HexReturnCoord.base 1 h0 (Or.inl rfl)
  simpa [HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.left] using h1

theorem hlha_finalDirection_sum_mod (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (d : HexReturnCoord) (H : ℤ)
    (hfinal : (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = d)
    (hcoord : halfStep H = d.value * halfStep 0) :
    (6 : ℤ) ∣ (ts.sum - H) := by
  have hbase : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hgeom := (hlhr_coordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base 0 (halfStep 0) 0 ts hbase hlegal).2
  rw [hfinal, ← hcoord] at hgeom
  have hunit : hexUnit (hexInfra_headAccum 0 ts) = hexUnit H := by
    exact hexInfra_halfStep_inj hgeom
  have hmod := (hexUnit_eq_iff_mod _ _).mp hunit
  simpa [hexInfra_headAccum_eq_add_sum] using hmod

theorem hlha_reverseDir_mod_h1 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨1, 1⟩) :
    (6 : ℤ) ∣ ts.sum - (-2) := by
  apply hlha_finalDirection_sum_mod ts hlegal ⟨-1, -1⟩ (-2)
  · have := congrArg hlha_negCoord hdir
    simpa using this
  · exact hlha_halfStep_coord_neg_two

theorem hlha_reverseDir_mod_h2 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨0, 1⟩) :
    (6 : ℤ) ∣ ts.sum - (-1) := by
  apply hlha_finalDirection_sum_mod ts hlegal ⟨0, -1⟩ (-1)
  · have := congrArg hlha_negCoord hdir
    simpa using this
  · exact hlha_halfStep_coord_neg_one

theorem hlha_reverseDir_mod_h3 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, 0⟩) :
    (6 : ℤ) ∣ ts.sum := by
  have h := hlha_finalDirection_sum_mod ts hlegal ⟨1, 0⟩ 0
    (by
      have hh := congrArg hlha_negCoord hdir
      simpa using hh)
    hlha_halfStep_coord_zero
  simpa using h

theorem hlha_reverseDir_mod_h4 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, -1⟩) :
    (6 : ℤ) ∣ ts.sum - 1 := by
  apply hlha_finalDirection_sum_mod ts hlegal ⟨1, 1⟩ 1
  · have := congrArg hlha_negCoord hdir
    simpa using this
  · exact hlha_halfStep_coord_one

noncomputable def hlha_reverseAugment (ts : List ℤ) : List ℤ :=
  match ts with
  | [] => hlha_emptyAugment
  | _ :: us =>
      let r := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts
      hlha_augmentSide (hlha_negCoord r.dir) (loopReverse us)

theorem hlha_prefixAugment_eq_reverseAugment (ts : List ℤ) :
    hlha_prefixAugment ts =
      hlha_reverseAugment (ts.take (hexW2_cutPos 0 ts)) := by
  unfold hlha_prefixAugment hlha_prefixReverseData hlha_reverseAugment
  generalize hp : ts.take (hexW2_cutPos 0 ts) = pre
  cases pre with
  | nil => rfl
  | cons t us =>
      simp only
      unfold hlha_cutState
      rw [hp]

theorem hlha_normTurns_injective (d : HexReturnCoord) :
    Function.Injective (hlha_normTurns d) := by
  intro xs ys h
  unfold hlha_normTurns at h
  split at h
  · have := congrArg hsc_negTurns h
    simpa only [hsc_negTurns_negTurns] using this
  · exact h

theorem hlha_augmentSide_injective_fixed (d : HexReturnCoord) :
    Function.Injective (hlha_augmentSide d) := by
  intro xs ys h
  apply hlha_normTurns_injective d
  have := congrArg (List.drop 2) h
  simpa [hlha_augmentSide] using this

theorem hlha_loopReverse_injective : Function.Injective loopReverse := by
  intro xs ys h
  have := congrArg loopReverse h
  simpa only [loopReverse_involutive] using this

theorem hlha_reverseDir_mod_cases (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (haway : HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir)) :
    (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨1, 1⟩ ∧
        (6 : ℤ) ∣ ts.sum - (-2)) ∨
      (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨0, 1⟩ ∧
        (6 : ℤ) ∣ ts.sum - (-1)) ∨
      (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, 0⟩ ∧
        (6 : ℤ) ∣ ts.sum) ∨
      (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, -1⟩ ∧
        (6 : ℤ) ∣ ts.sum - 1) := by
  rcases haway with h | h | h | h
  · exact Or.inl ⟨h, hlha_reverseDir_mod_h1 ts hlegal h⟩
  · exact Or.inr (Or.inl ⟨h, hlha_reverseDir_mod_h2 ts hlegal h⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨h, hlha_reverseDir_mod_h3 ts hlegal h⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨h, hlha_reverseDir_mod_h4 ts hlegal h⟩))

theorem hlha_negTurns_sum (ts : List ℤ) :
    (hsc_negTurns ts).sum = -ts.sum := by
  induction ts with
  | nil => simp [hsc_negTurns]
  | cons t ts ih =>
      unfold hsc_negTurns at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem hlha_cross_h1_h4_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨1, 1⟩ (loopReverse xs) =
      hlha_augmentSide ⟨-1, -1⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := congrArg List.sum h
  simp [hlha_augmentSide, hlha_normTurns, hlha_useSwap,
    hlha_cutTurn, loopReverse_sum, hlha_negTurns_sum] at hs
  omega

theorem hlha_cross_h4_h1_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨-1, -1⟩ (loopReverse xs) =
      hlha_augmentSide ⟨1, 1⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := hlha_cross_h1_h4_sum h.symm
  omega

theorem hlha_cross_h2_h3_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨0, 1⟩ (loopReverse xs) =
      hlha_augmentSide ⟨-1, 0⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := congrArg List.sum h
  simp [hlha_augmentSide, hlha_normTurns, hlha_useSwap,
    hlha_cutTurn, loopReverse_sum, hlha_negTurns_sum] at hs
  omega

theorem hlha_cross_h3_h2_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨-1, 0⟩ (loopReverse xs) =
      hlha_augmentSide ⟨0, 1⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := hlha_cross_h2_h3_sum h.symm
  omega




theorem hlha_reverseAugment_injective_of_away {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxaway : xs ≠ [] → HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir))
    (hyaway : ys ≠ [] → HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ys).dir))
    (heq : hlha_reverseAugment xs = hlha_reverseAugment ys) :
    xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlha_reverseAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlha_reverseAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
      | cons y ys =>
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          have hxcase := hlha_reverseDir_mod_cases (x :: xs) hxlegal
            (hxaway (by simp))
          have hycase := hlha_reverseDir_mod_cases (y :: ys) hylegal
            (hyaway (by simp))
          change hlha_augmentSide (hlha_negCoord
              (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (x :: xs)).dir)
                (loopReverse xs) =
            hlha_augmentSide (hlha_negCoord
              (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (y :: ys)).dir)
                (loopReverse ys) at heq
          rcases hxcase with ⟨hxd, hxm⟩ | ⟨hxd, hxm⟩ |
              ⟨hxd, hxm⟩ | ⟨hxd, hxm⟩ <;>
            rcases hycase with ⟨hyd, hym⟩ | ⟨hyd, hym⟩ |
              ⟨hyd, hym⟩ | ⟨hyd, hym⟩
          all_goals rw [hxd, hyd] at heq
          all_goals obtain ⟨kx, hkx⟩ := hxm
          all_goals obtain ⟨ky, hky⟩ := hym
          all_goals simp only [List.sum_cons] at hkx hky
          · have hi := hlha_augmentSide_injective_fixed ⟨1, 1⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hsum := hlha_cross_h1_h4_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hi := hlha_augmentSide_injective_fixed ⟨0, 1⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega
          · have hsum := hlha_cross_h2_h3_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hsum := hlha_cross_h3_h2_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · have hi := hlha_augmentSide_injective_fixed ⟨-1, 0⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hsum := hlha_cross_h4_h1_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hi := hlha_augmentSide_injective_fixed ⟨-1, -1⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega



noncomputable def hlha_forwardAugment (incoming : HexReturnCoord)
    (ts : List ℤ) : List ℤ :=
  match ts with
  | [] => hlha_emptyAugment
  | t :: us => hlha_augmentSide (incoming.turn t) us

theorem hlha_suffixAugment_eq_forwardAugment (ts : List ℤ) :
    hlha_suffixAugment ts =
      hlha_forwardAugment (hlha_cutState ts).dir
        (ts.drop (hexW2_cutPos 0 ts)) := by
  unfold hlha_suffixAugment hlha_forwardAugment
  generalize ts.drop (hexW2_cutPos 0 ts) = suffix
  cases suffix <;> rfl



theorem hlha_sourceTurn_eq_of_cutTurn_eq (incoming : HexReturnCoord)
    {t u : ℤ} (hi : incoming.IsUnit)
    (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1)
    (hdt : HLHAAwayDir (incoming.turn t))
    (hdu : HLHAAwayDir (incoming.turn u))
    (heq : hlha_cutTurn (incoming.turn t) =
      hlha_cutTurn (incoming.turn u)) : t = u := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp [HLHAAwayDir, hlha_cutTurn, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] at hdt hdu heq ⊢

theorem hlha_forwardAugment_injective_of_away (incoming : HexReturnCoord)
    (hi : incoming.IsUnit) {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxaway : ∀ t us, xs = t :: us → HLHAAwayDir (incoming.turn t))
    (hyaway : ∀ t us, ys = t :: us → HLHAAwayDir (incoming.turn t))
    (heq : hlha_forwardAugment incoming xs =
      hlha_forwardAugment incoming ys) : xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlha_forwardAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlha_forwardAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
      | cons y ys =>
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          have hdx := hxaway x xs rfl
          have hdy := hyaway y ys rfl
          change hlha_augmentSide (incoming.turn x) xs =
            hlha_augmentSide (incoming.turn y) ys at heq
          have hcut : hlha_cutTurn (incoming.turn x) =
              hlha_cutTurn (incoming.turn y) := by
            have hget := congrArg (fun l : List ℤ => l[1]?) heq
            simpa [hlha_augmentSide] using hget
          have hxy := hlha_sourceTurn_eq_of_cutTurn_eq incoming hi hx hy
            hdx hdy hcut
          subst y
          have htail := hlha_augmentSide_injective_fixed
            (incoming.turn x) heq
          rw [htail]



noncomputable def hlha_augmentedPair (ts : List ℤ) : List ℤ × List ℤ :=
  (hlha_prefixAugment ts, hlha_suffixAugment ts)

theorem hlha_prefix_reverse_away (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW)
    (hne : ts.take (hexW2_cutPos 0 ts) ≠ []) :
    HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (ts.take (hexW2_cutPos 0 ts))).dir) := by
  obtain ⟨t, us, hp⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hd, _⟩ := hlha_prefix_side_hypotheses a h0 ts hsource hp
  simpa [hlha_cutState] using hd

theorem hlha_suffix_forward_away (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) {t : ℤ} {us : List ℤ}
    (hs : ts.drop (hexW2_cutPos 0 ts) = t :: us) :
    HLHAAwayDir ((hlha_cutState ts).dir.turn t) :=
  (hlha_suffix_side_hypotheses a h0 ts hsource hs).1

theorem hlha_augmentedPair_injective (a : ℂ) (h0 : ℤ)
    {xs ys : List ℤ}
    (hx : (ofTurns a h0 xs).IsLegalSAW)
    (hy : (ofTurns a h0 ys).IsLegalSAW)
    (heq : hlha_augmentedPair xs = hlha_augmentedPair ys) : xs = ys := by
  have hpreAug := congrArg Prod.fst heq
  have hsufAug := congrArg Prod.snd heq
  let px := xs.take (hexW2_cutPos 0 xs)
  let py := ys.take (hexW2_cutPos 0 ys)
  have hpxlegal : ∀ t ∈ px, t = 1 ∨ t = -1 := by
    intro t ht
    exact hx.1 t (List.mem_of_mem_take ht)
  have hpylegal : ∀ t ∈ py, t = 1 ∨ t = -1 := by
    intro t ht
    exact hy.1 t (List.mem_of_mem_take ht)
  have hpre : px = py := by
    apply hlha_reverseAugment_injective_of_away hpxlegal hpylegal
    · intro hne
      exact hlha_prefix_reverse_away a h0 xs hx hne
    · intro hne
      exact hlha_prefix_reverse_away a h0 ys hy hne
    · rw [← hlha_prefixAugment_eq_reverseAugment,
        ← hlha_prefixAugment_eq_reverseAugment]
      exact hpreAug
  have hcpx : (px.length = hexW2_cutPos 0 xs) := by
    simp [px, List.length_take_of_le (hexW2_cutPos_le 0 xs)]
  have hcpy : (py.length = hexW2_cutPos 0 ys) := by
    simp [py, List.length_take_of_le (hexW2_cutPos_le 0 ys)]
  have hcp : hexW2_cutPos 0 xs = hexW2_cutPos 0 ys := by
    rw [← hcpx, ← hcpy, hpre]
  let r := hlha_cutState xs
  have hr : hlha_cutState ys = r := by
    unfold hlha_cutState r
    exact congrArg (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base) hpre.symm
  have hrunit : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base px HexReturnCoord.base_isUnit hpxlegal
  let sx := xs.drop (hexW2_cutPos 0 xs)
  let sy := ys.drop (hexW2_cutPos 0 ys)
  have hsxlegal : ∀ t ∈ sx, t = 1 ∨ t = -1 := by
    intro t ht
    exact hx.1 t (List.mem_of_mem_drop ht)
  have hsylegal : ∀ t ∈ sy, t = 1 ∨ t = -1 := by
    intro t ht
    exact hy.1 t (List.mem_of_mem_drop ht)
  have hsuf : sx = sy := by
    apply hlha_forwardAugment_injective_of_away r.dir hrunit
      hsxlegal hsylegal
    · intro t us hs
      exact hlha_suffix_forward_away a h0 xs hx hs
    · intro t us hs
      have ha := hlha_suffix_forward_away a h0 ys hy hs
      rw [hr] at ha
      exact ha
    · calc
        hlha_forwardAugment r.dir sx = hlha_suffixAugment xs := by
          symm
          simpa [r, sx] using hlha_suffixAugment_eq_forwardAugment xs
        _ = hlha_suffixAugment ys := by
          simpa [hlha_augmentedPair] using hsufAug
        _ = hlha_forwardAugment r.dir sy := by
          rw [hlha_suffixAugment_eq_forwardAugment, hr]
  have hxs : xs = px ++ sx := by
    simpa [px, sx] using
      (List.take_append_drop (hexW2_cutPos 0 xs) xs).symm
  have hys : py ++ sy = ys := by
    simpa [py, sy] using List.take_append_drop (hexW2_cutPos 0 ys) ys
  exact hxs.trans ((congrArg₂ List.append hpre hsuf).trans hys)




@[simp] theorem hlha_prefixAugment_cons_tail (ts : List ℤ) :
    (-1 : ℤ) :: (hlha_prefixAugment ts).tail = hlha_prefixAugment ts := by
  unfold hlha_prefixAugment hlha_prefixReverseData
  generalize ts.take (hexW2_cutPos 0 ts) = pre
  cases pre <;> simp [hlha_emptyAugment, hlha_augmentSide]


@[simp] theorem hlha_suffixAugment_cons_tail (ts : List ℤ) :
    (-1 : ℤ) :: (hlha_suffixAugment ts).tail = hlha_suffixAugment ts := by
  unfold hlha_suffixAugment
  generalize ts.drop (hexW2_cutPos 0 ts) = suf
  cases suf <;> simp [hlha_emptyAugment, hlha_augmentSide]




noncomputable def hlha_decodePair (a : ℂ) (h0 : ℤ)
    (p : List ℤ × List ℤ) : List ℤ := by
  classical
  exact if h : ∃ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW ∧ hlha_augmentedPair ts = p then
    Classical.choose h
  else []

@[simp] theorem hlha_decodePair_augmented (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    hlha_decodePair a h0 (hlha_augmentedPair ts) = ts := by
  classical
  unfold hlha_decodePair
  rw [dif_pos ⟨ts, hsource, rfl⟩]
  let h : ∃ us : List ℤ,
      (ofTurns a h0 us).IsLegalSAW ∧
        hlha_augmentedPair us = hlha_augmentedPair ts :=
    ⟨ts, hsource, rfl⟩
  have hchosen := Classical.choose_spec h
  exact hlha_augmentedPair_injective a h0 hchosen.1 hsource hchosen.2



noncomputable def hlha_decodeAugmented (a : ℂ) (h0 : ℤ)
    (lowerBoundary : ℤ) (lowerCore : List ℤ)
    (upperBoundary : ℤ) (upperCore : List ℤ) : List ℤ :=
  hlha_decodePair a h0
    (lowerBoundary :: lowerCore, upperBoundary :: upperCore)


theorem hlha_augmentedCore_length (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    (hlha_prefixAugment ts).tail.length +
        (hlha_suffixAugment ts).tail.length = ts.length := by
  have hp := (hlha_prefixAugment_spec a h0 ts hsource).2.2
  have hs := (hlha_suffixAugment_spec a h0 ts hsource).2.2
  have hpc := congrArg List.length (hlha_prefixAugment_cons_tail ts)
  have hsc := congrArg List.length (hlha_suffixAugment_cons_tail ts)
  have hsplit := congrArg List.length
    (List.take_append_drop (hexW2_cutPos 0 ts) ts)
  simp only [List.length_cons, List.length_append] at hpc hsc hsplit
  omega





noncomputable def hlha_augmentedTwoHalfData (a : ℂ) (h0 : ℤ) (N : ℕ) :
    HLHRAugmentedTwoHalfData a h0 N where
  lowerBoundary := fun _ => -1
  upperBoundary := fun _ => -1
  lowerCore := fun d => (hlha_prefixAugment d.1).tail
  upperCore := fun d => (hlha_suffixAugment d.1).tail
  decode := hlha_decodeAugmented a h0
  decode_source := by
    intro d
    have hsource := (hhc_Dn_spec a h0 N d).1
    simp only [hlha_decodeAugmented]
    rw [hlha_prefixAugment_cons_tail, hlha_suffixAugment_cons_tail]
    exact hlha_decodePair_augmented a h0 d.1 hsource
  core_length := by
    intro d
    exact hlha_augmentedCore_length a h0 d.1 (hhc_Dn_spec a h0 N d).1
  lower_legal := by
    intro d
    rw [hlha_prefixAugment_cons_tail]
    exact (hlha_prefixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).1
  upper_legal := by
    intro d
    rw [hlha_suffixAugment_cons_tail]
    exact (hlha_suffixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).1
  lower_halfSpace := by
    intro d
    rw [hlha_prefixAugment_cons_tail]
    exact (hlha_prefixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).2.1
  upper_halfSpace := by
    intro d
    rw [hlha_suffixAugment_cons_tail]
    exact (hlha_suffixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).2.1



theorem hlha_finite_partial_bound (a : ℂ) (h0 : ℤ) (N : ℕ)
    {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ 2)⁻¹ *
        ((∑ s ∈ (hlha_augmentedTwoHalfData a h0 N).lowerImage,
            hhc_halfWeight x s) *
          (∑ s ∈ (hlha_augmentedTwoHalfData a h0 N).upperImage,
            hhc_halfWeight x s)) := by
  exact (hlha_augmentedTwoHalfData a h0 N).finite_partial_bound hx

end StatMech.Universality
