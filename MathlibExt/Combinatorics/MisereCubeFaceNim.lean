/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CubeNim
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import all MathlibExt.GameTheory.BoutonNim
import MathlibExt.GameTheory.ImpartialAcyclicGame

/-!
# Misère face Nim on a cube

A face move reduces exactly one heap. With at least two large heaps the usual Nim move
still works; with just one large heap the move must instead leave an odd number of ones.

## References

* Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
  INTEGERS 25 (2025), Article G2, pp. 1–14, Theorem 9 (p. 9).
* Charles L. Bouton, *Nim, A Game with a Complete Mathematical Theory*, Annals of Mathematics
  (2) 3 (1901–1902), no. 1/4, pp. 35–39, §§2, 5–6, for the original Nim and misère Nim analyses.
* Tanya Khovanova and Joshua Xiong, *Nim Fractals*, Journal of Integer Sequences 17 (2014),
  Article 14.7.8, §2, Theorem 4, for the normal-play classification.
-/

namespace MetaMathlibExt

private abbrev FacePosition := Fin 6 → ℕ

private def faceNimSum (p : FacePosition) : ℕ := (List.ofFn p).foldl Nat.xor 0

private theorem faceNimSum_eq (p : FacePosition) :
    faceNimSum p = p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 := by
  change [p 0, p 1, p 2, p 3, p 4, p 5].foldl Nat.xor 0 = _
  simp only [List.foldl_cons, List.foldl_nil]
  change 0 ^^^ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = _
  rw [Nat.zero_xor]

private def HasLargeFace (p : FacePosition) : Prop := ∃ i, 2 ≤ p i

private def MisereFaceLosing (p : FacePosition) : Prop :=
  (HasLargeFace p ∧ faceNimSum p = 0) ∨ (¬ HasLargeFace p ∧ faceNimSum p = 1)

private theorem faceMove_iff_update {p q : FacePosition} :
    CubeFaceMove p q ↔ ∃ i a, a < p i ∧ q = Function.update p i a := by
  constructor
  · rintro ⟨i, hle, hne, hfix⟩
    have heq : q = Function.update p i (q i) := by
      ext j
      obtain rfl | hj := eq_or_ne j i
      · simp
      · simpa [Function.update_of_ne hj] using hfix j hj
    refine ⟨i, q i, lt_of_le_of_ne (hle i) ?_, heq⟩
    intro hi
    exact hne (by simpa [hi] using heq)
  · rintro ⟨i, a, ha, rfl⟩
    refine ⟨i, ?_, Function.update_ne_self_iff.mpr ha.ne, fun _ hj => Function.update_of_ne hj _ _⟩
    intro j
    obtain rfl | hj := eq_or_ne j i
    · simpa using ha.le
    · simp [Function.update_of_ne hj]

private theorem set_ofFn_face (p : FacePosition) (i : Fin 6) (a : ℕ) :
    (List.ofFn p).set i a = List.ofFn (Function.update p i a) := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
  by_cases h : (i : ℕ) = j
  · have heq : (⟨j, by simpa using hj'⟩ : Fin 6) = i := Fin.ext h.symm
    simp [h, heq]
  · have hne : (⟨j, by simpa using hj'⟩ : Fin 6) ≠ i :=
      fun heq => h (congrArg Fin.val heq).symm
    simp [h, Function.update_of_ne hne]

private theorem get_ofFn_face (p : FacePosition) (i : Fin (List.ofFn p).length) :
    (List.ofFn p).get i = p (i.cast List.length_ofFn) := by
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  rfl

private theorem faceNimSum_update (p : FacePosition) (i : Fin 6) (a : ℕ) :
    faceNimSum (Function.update p i a) = faceNimSum p ^^^ p i ^^^ a := by
  have h := BoutonNim.foldl_set_fin (List.ofFn p) (i.cast List.length_ofFn.symm) a
  rw [Fin.val_cast, set_ofFn_face p i a, get_ofFn_face] at h
  exact h

private theorem faceNimSum_lt_two {p : FacePosition} (h : ¬ HasLargeFace p) : faceNimSum p < 2 := by
  have hs (i : Fin 6) : p i < 2 ^ 1 := lt_of_not_ge fun hi => h ⟨i, hi⟩
  rw [faceNimSum_eq]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hs 0) (hs 1)) (hs 2)) (hs 3)) (hs 4)) (hs 5)

private theorem no_large_update {p : FacePosition} {i : Fin 6} {a : ℕ} (ha : a < 2)
    (h : ∀ j, j ≠ i → p j < 2) : ¬ HasLargeFace (Function.update p i a) := by
  rintro ⟨j, hj⟩
  obtain rfl | hji := eq_or_ne j i
  · exact (not_le_of_gt ha) (by simpa using hj)
  · exact (not_le_of_gt (h j hji)) (by simpa [Function.update_of_ne hji] using hj)

private theorem exists_other_large_of_zero {p : FacePosition} {i : Fin 6}
    (hzero : faceNimSum p = 0) (hi : 2 ≤ p i) : ∃ j, j ≠ i ∧ 2 ≤ p j := by
  by_contra! h
  have hsmall := faceNimSum_lt_two (no_large_update (a := 0) (by decide) h)
  rw [faceNimSum_update, hzero, Nat.zero_xor, Nat.xor_zero] at hsmall
  exact (not_lt_of_ge hi) hsmall

private theorem large_survives {p : FacePosition} (i j : Fin 6) (hij : i ≠ j)
    (hi : 2 ≤ p i) (hj : 2 ≤ p j) (k : Fin 6) (a : ℕ) :
    HasLargeFace (Function.update p k a) := by
  obtain rfl | hik := eq_or_ne i k
  · exact ⟨j, by simpa [Function.update_of_ne hij.symm] using hj⟩
  · exact ⟨i, by simpa [Function.update_of_ne hik] using hi⟩

private theorem face_losing_stable {p q : FacePosition} (hp : MisereFaceLosing p)
    (hm : CubeFaceMove p q) : ¬ MisereFaceLosing q := by
  have hle : q ≤ p := by
    obtain ⟨_, h, -, -⟩ := hm
    exact h
  obtain ⟨i, a, ha, rfl⟩ := faceMove_iff_update.mp hm
  rintro (⟨hlarge, hzero⟩ | ⟨hsmall, hone⟩)
  · rcases hp with ⟨_, hp⟩ | ⟨hp, _⟩
    · rw [faceNimSum_update, hp, Nat.zero_xor] at hzero
      exact ha.ne (xor_eq_zero_iff.mp hzero).symm
    · obtain ⟨j, hj⟩ := hlarge
      exact hp ⟨j, hj.trans (hle j)⟩
  · rcases hp with ⟨⟨j, hj⟩, hp⟩ | ⟨hp, hpone⟩
    · obtain ⟨k, hkj, hk⟩ := exists_other_large_of_zero hp hj
      exact hsmall (large_survives k j hkj hk hj i a)
    · have hpi : p i < 2 := lt_of_not_ge fun h => hp ⟨i, h⟩
      have hi : p i = 1 := by omega
      have ha' : a = 0 := by omega
      simp [faceNimSum_update, hpone, hi, ha'] at hone

private theorem face_losing_nonzero {p : FacePosition} (hp : MisereFaceLosing p) : p ≠ 0 := by
  rintro rfl
  simp [MisereFaceLosing, HasLargeFace, faceNimSum_eq] at hp

private theorem exists_face_move_of_ne_zero {p : FacePosition} (hp : p ≠ 0) :
    ∃ q, CubeFaceMove p q := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
  exact ⟨_, faceMove_iff_update.mpr ⟨i, 0, Nat.pos_of_ne_zero hi, rfl⟩⟩

private theorem face_move_to_losing {p : FacePosition} (hp : p ≠ 0) (hn : ¬ MisereFaceLosing p) :
    ∃ q, CubeFaceMove p q ∧ MisereFaceLosing q := by
  by_cases hlarge : HasLargeFace p
  · obtain ⟨i, hi⟩ := hlarge
    by_cases hother : ∃ j, j ≠ i ∧ 2 ≤ p j
    · -- Bouton's move leaves at least one of the two large heaps unchanged.
      obtain ⟨j, hji, hj⟩ := hother
      have hzero : faceNimSum p ≠ 0 := fun h => hn (Or.inl ⟨⟨i, hi⟩, h⟩)
      obtain ⟨k, a, ha, hx⟩ := (BoutonNim.bouton_nim_p_positions (List.ofFn p)).2 hzero
      let k' : Fin 6 := k.cast List.length_ofFn
      rw [get_ofFn_face] at ha
      rw [← show (k' : ℕ) = k.val from rfl, set_ofFn_face] at hx
      exact ⟨_, faceMove_iff_update.mpr ⟨k', a, ha, rfl⟩,
        Or.inl ⟨large_survives j i hji hj hi k' a, hx⟩⟩
    · -- Choose the new heap size in {0, 1} so that the remaining xor is one.
      push Not at hother
      let a := faceNimSum (Function.update p i 0) ^^^ 1
      have ha : a < 2 := Nat.xor_lt_two_pow
        (faceNimSum_lt_two (no_large_update (a := 0) (by decide) hother)) (by decide : 1 < 2 ^ 1)
      refine ⟨_, faceMove_iff_update.mpr ⟨i, a, ha.trans_le hi, rfl⟩,
        Or.inr ⟨no_large_update ha hother, ?_⟩⟩
      simp only [a, faceNimSum_update, Nat.xor_zero, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · -- With only unit heaps, removing one flips the xor from zero to one.
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
    change p i ≠ 0 at hi
    have hlt (j : Fin 6) : p j < 2 := lt_of_not_ge fun h => hlarge ⟨j, h⟩
    have hpi : p i = 1 := by have := hlt i; omega
    have hxor : faceNimSum p = 0 := by
      have hlt := faceNimSum_lt_two hlarge
      have hne : faceNimSum p ≠ 1 := fun h => hn (Or.inr ⟨hlarge, h⟩)
      omega
    refine ⟨_, faceMove_iff_update.mpr ⟨i, 0, Nat.pos_of_ne_zero hi, rfl⟩,
      Or.inr ⟨no_large_update (by decide) (fun j _ => hlt j), ?_⟩⟩
    simp [faceNimSum_update, hxor, hpi]

private theorem faceMove_total_lt {p q : FacePosition} (h : CubeFaceMove p q) :
    (∑ i, q i) < ∑ i, p i := by
  obtain ⟨_, hle, hne, _⟩ := h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hle i) hi⟩

private theorem misere_face_classification (P : Set FacePosition)
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)
    (p : FacePosition) : p ∈ P ↔ MisereFaceLosing p := by
  -- Restrict to nonterminal positions: then each losing set is a kernel of the move relation.
  have hp_ne_zero {q : FacePosition} (hq : q ∈ P) : q ≠ 0 := by
    rintro rfl
    obtain ⟨r, hr⟩ := ((hP 0).mp hq).1
    exact (cubeVertexEdgeFaceMove_examples.2.2.2 r).2.2 hr
  classical
  let Live := {q : FacePosition // q ≠ 0}
  let move (x y : Live) := CubeFaceMove x.val y.val
  let rank (x : Live) : ℕ := ∑ i, x.val i
  have hwf : WellFounded (fun y x : Live => move x y) :=
    (measure rank).wf.mono fun _ _ h => faceMove_total_lt h
  have heq : ({x : Live | x.val ∈ P} : Set Live) = {x | MisereFaceLosing x.val} := by
    apply pPositions_unique move hwf
    · exact fun x y hx hm => ((hP x.val).mp hx).2 y.val hm
    · intro x hx
      by_contra! hn
      apply hx
      apply (hP x.val).mpr
      exact ⟨exists_face_move_of_ne_zero x.property,
        fun y hy hyP => hn ⟨y, hp_ne_zero hyP⟩ hy hyP⟩
    · exact fun _ _ hx hm => face_losing_stable hx hm
    · intro x hx
      obtain ⟨y, hy, hlose⟩ := face_move_to_losing x.property hx
      exact ⟨⟨y, face_losing_nonzero hlose⟩, hy, hlose⟩
  by_cases hp : p = 0
  · subst p
    exact iff_of_false (fun h => hp_ne_zero h rfl) (fun h => face_losing_nonzero h rfl)
  · change (⟨p, hp⟩ : Live) ∈ ({x : Live | x.val ∈ P} : Set Live) ↔
      (⟨p, hp⟩ : Live) ∈ ({x : Live | MisereFaceLosing x.val} : Set Live)
    rw [heq]

@[expose] public section

-- The three order hypotheses are retained for the published normalization; only maximality is used.
set_option linter.unusedVariables false in
/-- **Misère P-positions of face Nim on a cube.** Write positions of the game $C_F$ (Nim with six
heaps) as tuples $p = (a, b, c, A, B, C)$ of numbers of tokens on the faces
$f_a, f_b, f_c, f_A, f_B, f_C$, where $f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and let
$\oplus$ be the Nim-sum (bitwise exclusive or) of natural numbers. Let $\mathcal P$ be any set
of positions such that a position lies in $\mathcal P$ if and only if it has a face move and
every face move from it leads to a position outside $\mathcal P$; this is the set of
P-positions under misère play, where the player making the last move loses. Let $p$ be a
position in which every entry is at most $C$, and $a \le A$, $b \le B$ and $a \le b$. Then
$p \in \mathcal P$ if and only if either $C \ge 2$ and $a \oplus b \oplus c \oplus A \oplus B
\oplus C = 0$, or $C < 2$ and $a \oplus b \oplus c \oplus A \oplus B \oplus C = 1$.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 9 (`integers-2025-G2-thm-9`). -/
public theorem cubeFaceNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (2 ≤ p 5 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 0) ∨
      (p 5 < 2 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 1) := by
  have hlarge : HasLargeFace p ↔ 2 ≤ p 5 :=
    ⟨fun ⟨i, hi⟩ => hi.trans (hC i), fun hi => ⟨5, hi⟩⟩
  simp only [misere_face_classification P hP, MisereFaceLosing, hlarge, not_le, faceNimSum_eq]

end

end MetaMathlibExt
