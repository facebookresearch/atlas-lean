/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup

/-!
# Multiplication at the penultimate face index

Let X be a Kan simplicial set in universe u, x a vertex, and n∈ℕ. Pointed (n+2)-simplices p,q,r
are maps Δ[n+2]→X constant at x on the boundary. A multiplication triangle at the penultimate
index n gives the same product [p][q]=[r] in π_{n+2}(X,x) as the multiplication defined at the
final index n+1.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial

namespace SSet.PtSimplex.MulStruct

variable {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
  {p q r rLast : X.PtSimplex (n + 2) x}

private def g (n : ℕ) (t : Fin 5) : Fin (n + 5) :=
  ⟨n + t, by omega⟩

private def l (n : ℕ) (t : Fin 4) : Fin (n + 4) :=
  ⟨n + t, by omega⟩

private def s (n : ℕ) (t : Fin 3) : Fin (n + 3) :=
  ⟨n + t, by omega⟩

@[simp] private lemma g_val (n : ℕ) (t : Fin 5) : (g n t).val = n + t := rfl
@[simp] private lemma l_val (n : ℕ) (t : Fin 4) : (l n t).val = n + t := rfl
@[simp] private lemma s_val (n : ℕ) (t : Fin 3) : (s n t).val = n + t := rfl

private lemma g_castSucc_l (n : ℕ) (t : Fin 4) :
    g n t.castSucc = (l n t).castSucc := by
  apply Fin.ext
  simp [g, l]

private lemma g1_succ_l0 (n : ℕ) : g n 1 = (l n 0).succ := by
  apply Fin.ext
  simp [g, l]

private lemma g1_castSucc_l1 (n : ℕ) : g n 1 = (l n 1).castSucc := by
  apply Fin.ext
  simp [g, l]

private lemma g2_succ_l1 (n : ℕ) : g n 2 = (l n 1).succ := by
  apply Fin.ext
  simp [g, l]

private lemma g3_succ_l2 (n : ℕ) : g n 3 = (l n 2).succ := by
  apply Fin.ext
  simp [g, l]

private lemma g4_succ_l3 (n : ℕ) : g n 4 = (l n 3).succ := by
  apply Fin.ext
  simp [g, l]

private lemma g_cast0_g0 (n : ℕ) : g n (Fin.castSucc (0 : Fin 4)) = g n 0 := by
  apply Fin.ext
  simp [g]

private lemma g0_cast_l0 (n : ℕ) : g n 0 = (l n 0).castSucc := by
  apply Fin.ext
  simp [g, l]

private lemma g1_cast_l1 (n : ℕ) : g n 1 = (l n 1).castSucc := by
  apply Fin.ext
  simp [g, l]

private lemma g2_cast_l2 (n : ℕ) : g n 2 = (l n 2).castSucc := by
  apply Fin.ext
  simp [g, l]

@[simp] private lemma g2_pred (n : ℕ) (h : g n 2 ≠ 0) :
    (g n 2).pred h = l n 1 := by apply Fin.ext; simp [g, l]
@[simp] private lemma g3_pred (n : ℕ) (h : g n 3 ≠ 0) :
    (g n 3).pred h = l n 2 := by apply Fin.ext; simp [g, l]
@[simp] private lemma g4_pred (n : ℕ) (h : g n 4 ≠ 0) :
    (g n 4).pred h = l n 3 := by apply Fin.ext; simp [g, l]
@[simp] private lemma g0_castPred (n : ℕ) (h : g n 0 ≠ Fin.last (n + 4)) :
    (g n 0).castPred h = l n 0 := by apply Fin.ext; simp [g, l]
@[simp] private lemma g1_pred (n : ℕ) (h : g n 1 ≠ 0) :
    (g n 1).pred h = l n 0 := by apply Fin.ext; simp [g, l]
@[simp] private lemma g1_castPred (n : ℕ) (h : g n 1 ≠ Fin.last (n + 4)) :
    (g n 1).castPred h = l n 1 := by apply Fin.ext; simp [g, l]
@[simp] private lemma g2_castPred (n : ℕ) (h : g n 2 ≠ Fin.last (n + 4)) :
    (g n 2).castPred h = l n 2 := by apply Fin.ext; simp [g, l]
@[simp] private lemma g3_castPred (n : ℕ) (h : g n 3 ≠ Fin.last (n + 4)) :
    (g n 3).castPred h = l n 3 := by apply Fin.ext; simp [g, l]

private lemma l_castSucc (n : ℕ) (t : Fin 3) :
    l n t.castSucc = (s n t).castSucc := by
  apply Fin.ext
  simp [l, s]

private lemma l_succ (n : ℕ) (t : Fin 3) :
    l n t.succ = (s n t).succ := by
  apply Fin.ext
  simp only [l, s, Fin.succ_mk]
  change n + (t.val + 1) = n + t.val + 1
  omega

private def D (z : X.PtSimplex (n + 2) x) (t : Fin 3) :
    (Δ[n + 3] : SSet.{u}) ⟶ X :=
  (RelStruct.refl z (s n t)).map

@[reassoc (attr := simp)]
private lemma δ_D_castSucc (z : X.PtSimplex (n + 2) x) (t : Fin 3) :
    stdSimplex.δ (l n t.castSucc) ≫ D z t = z.map := by
  rw [l_castSucc]
  exact (RelStruct.refl z (s n t)).δ_castSucc_map

@[reassoc (attr := simp)]
private lemma δ_D_succ (z : X.PtSimplex (n + 2) x) (t : Fin 3) :
    stdSimplex.δ (l n t.succ) ≫ D z t = z.map := by
  rw [l_succ]
  exact (RelStruct.refl z (s n t)).δ_succ_map

@[simp] private lemma δ_D_l0 (z : X.PtSimplex (n + 2) x) :
    stdSimplex.δ (l n 0) ≫ D z 0 = z.map := by
  change stdSimplex.δ (l n (0 : Fin 3).castSucc) ≫ D z 0 = z.map
  exact δ_D_castSucc z 0

@[simp] private lemma δ_D_l1_left (z : X.PtSimplex (n + 2) x) :
    stdSimplex.δ (l n 1) ≫ D z 0 = z.map := by
  change stdSimplex.δ (l n (0 : Fin 3).succ) ≫ D z 0 = z.map
  exact δ_D_succ z 0

@[simp] private lemma δ_D_l1_right (z : X.PtSimplex (n + 2) x) :
    stdSimplex.δ (l n 1) ≫ D z 1 = z.map := by
  change stdSimplex.δ (l n (1 : Fin 3).castSucc) ≫ D z 1 = z.map
  exact δ_D_castSucc z 1

@[simp] private lemma δ_D_l2_left (z : X.PtSimplex (n + 2) x) :
    stdSimplex.δ (l n 2) ≫ D z 1 = z.map := by
  change stdSimplex.δ (l n (1 : Fin 3).succ) ≫ D z 1 = z.map
  exact δ_D_succ z 1

@[simp] private lemma δ_D_l2_right (z : X.PtSimplex (n + 2) x) :
    stdSimplex.δ (l n 2) ≫ D z 2 = z.map := by
  change stdSimplex.δ (l n (2 : Fin 3).castSucc) ≫ D z 2 = z.map
  exact δ_D_castSucc z 2

@[simp] private lemma δ_D_l3 (z : X.PtSimplex (n + 2) x) :
    stdSimplex.δ (l n 3) ≫ D z 2 = z.map := by
  change stdSimplex.δ (l n (2 : Fin 3).succ) ≫ D z 2 = z.map
  exact δ_D_succ z 2

@[reassoc]
private lemma δ_D_of_lt (z : X.PtSimplex (n + 2) x) (t : Fin 3)
    (j : Fin (n + 4)) (hj : j < l n t.castSucc) :
    stdSimplex.δ j ≫ D z t = SSet.const x := by
  rw [l_castSucc] at hj
  exact (RelStruct.refl z (s n t)).δ_map_of_lt j hj

@[reassoc]
private lemma δ_D_of_gt (z : X.PtSimplex (n + 2) x) (t : Fin 3)
    (j : Fin (n + 4)) (hj : l n t.succ < j) :
    stdSimplex.δ j ≫ D z t = SSet.const x := by
  rw [l_succ] at hj
  exact (RelStruct.refl z (s n t)).δ_map_of_gt j hj

private lemma l_pen0 (n : ℕ) :
    l n 0 = (Fin.last n).castSucc.castSucc.castSucc := by
  apply Fin.ext
  simp [l]

private lemma l_pen1 (n : ℕ) :
    l n 1 = (Fin.last n).castSucc.castSucc.succ := by
  apply Fin.ext
  simp [l]

private lemma l_pen2 (n : ℕ) :
    l n 2 = (Fin.last n).castSucc.succ.succ := by
  apply Fin.ext
  simp [l]

private lemma l_last1 (n : ℕ) :
    l n 1 = (Fin.last (n + 1)).castSucc.castSucc := by
  apply Fin.ext
  simp [l]

private lemma l_last2 (n : ℕ) :
    l n 2 = (Fin.last (n + 1)).castSucc.succ := by
  apply Fin.ext
  simp [l]

private lemma l_last3 (n : ℕ) :
    l n 3 = (Fin.last (n + 1)).succ.succ := by
  apply Fin.ext
  simp [l]

@[simp] private lemma hPen_face_q
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 0) ≫ h.map = q.map := by
  rw [l_pen0]
  exact h.δ_castSucc_castSucc_map

@[simp] private lemma hPen_face_r
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 1) ≫ h.map = r.map := by
  rw [l_pen1]
  exact h.δ_succ_castSucc_map

@[simp] private lemma hPen_face_p
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 2) ≫ h.map = p.map := by
  rw [l_pen2]
  exact h.δ_succ_succ_map

private lemma hPen_face_const_of_lt
    (h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 4)) (hj : j < l n 0) :
    stdSimplex.δ j ≫ h.map = SSet.const x := by
  rw [l_pen0] at hj
  exact h.δ_map_of_lt j hj

private lemma hPen_face_const_of_gt
    (h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 4)) (hj : l n 2 < j) :
    stdSimplex.δ j ≫ h.map = SSet.const x := by
  rw [l_pen2] at hj
  exact h.δ_map_of_gt j hj

private lemma hLast_face_q
    (h : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 1) ≫ h.map = q.map := by
  rw [l_last1]
  exact h.δ_castSucc_castSucc_map

private lemma hLast_face_r
    (h : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 2) ≫ h.map = rLast.map := by
  rw [l_last2]
  exact h.δ_succ_castSucc_map

private lemma hLast_face_p
    (h : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 3) ≫ h.map = p.map := by
  rw [l_last3]
  exact h.δ_succ_succ_map

private lemma hLast_face_const_of_lt
    (h : MulStruct p q rLast (Fin.last (n + 1)))
    (j : Fin (n + 4)) (hj : j < l n 1) :
    stdSimplex.δ j ≫ h.map = SSet.const x := by
  rw [l_last1] at hj
  exact h.δ_map_of_lt j hj

private def A_faces (h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 5)) (_ : j ≠ g n 1) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j = g n 0 then D q 2 else
  if j = g n 2 then D p 1 else
  if j = g n 3 then h.map else
  if j = g n 4 then D q 0 else
  SSet.const x

private lemma A_cases (j : Fin (n + 5)) (hj : j ≠ g n 1) :
    j < g n 0 ∨ j = g n 0 ∨ j = g n 2 ∨ j = g n 3 ∨ j = g n 4 := by
  by_cases hpre : j.val < n
  · exact Or.inl hpre
  have hne : j.val ≠ n + 1 := by
    intro h
    apply hj
    apply Fin.ext
    simpa [g] using h
  have hv : j.val = n ∨ j.val = n + 2 ∨ j.val = n + 3 ∨ j.val = n + 4 := by
    have := j.isLt
    omega
  rcases hv with h | h | h | h
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

private lemma lt_g0_ne_g1 {j : Fin (n + 5)} (hj : j < g n 0) :
    j ≠ g n 1 := by
  intro h
  subst j
  simp [Fin.lt_def, g] at hj

private lemma A_faces_of_lt (h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 5)) (hj : j < g n 0) :
    A_faces h j (lt_g0_ne_g1 hj) = SSet.const x := by
  have h0 : j ≠ g n 0 := ne_of_lt hj
  have h2 : j ≠ g n 2 := by
    intro hEq
    subst j
    simp [Fin.lt_def, g] at hj
  have h3 : j ≠ g n 3 := by
    intro hEq
    subst j
    simp [Fin.lt_def, g] at hj
  have h4 : j ≠ g n 4 := by
    intro hEq
    subst j
    simp [Fin.lt_def, g] at hj
  simp [A_faces, h0, h2, h3, h4]

private lemma A_faces_g0 (h : MulStruct p q r (Fin.last n).castSucc) :
    A_faces h (g n 0) (by simp [g]) = D q 2 := by simp [A_faces, g]

private lemma A_faces_g2 (h : MulStruct p q r (Fin.last n).castSucc) :
    A_faces h (g n 2) (by simp [g]) = D p 1 := by simp [A_faces, g]

private lemma A_faces_g3 (h : MulStruct p q r (Fin.last n).castSucc) :
    A_faces h (g n 3) (by simp [g]) = h.map := by simp [A_faces, g]

private lemma A_faces_g4 (h : MulStruct p q r (Fin.last n).castSucc) :
    A_faces h (g n 4) (by simp [g]) = D q 0 := by simp [A_faces, g]

private lemma A_face_of_prefix (h : MulStruct p q r (Fin.last n).castSucc)
    (j k : Fin (n + 5)) (hj : j < g n 0) (hjk : j < k)
    (hk : k ≠ g n 1) :
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ A_faces h k hk =
      SSet.const x := by
  have hjv : j.val < n := by simpa [Fin.lt_def, g] using hj
  rcases A_cases k hk with hk' | rfl | rfl | rfl | rfl
  · rw [A_faces_of_lt h k hk', comp_const]
  · rw [A_faces_g0]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [A_faces_g2]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [A_faces_g3]
    apply hPen_face_const_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [A_faces_g4]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega

private lemma A_compatible (h : MulStruct p q r (Fin.last n).castSucc) :
    horn.IsCompatible (fun j hj ↦ A_faces h j hj) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  by_cases hj' : j < g n 0
  · rw [A_faces_of_lt h j hj', comp_const]
    exact (A_face_of_prefix h j k hj' hjk hk).symm
  rcases A_cases j hj with hj'' | rfl | rfl | rfl | rfl
  · exact (hj' hj'').elim
  all_goals rcases A_cases k hk with hk' | rfl | rfl | rfl | rfl
  all_goals try { simp only [Fin.lt_def, g_val] at hjk; omega }
  all_goals simp only [A_faces_g0, A_faces_g2, A_faces_g3, A_faces_g4]
  all_goals try simp only [g2_pred, g3_pred, g4_pred,
    g0_castPred, g2_castPred, g3_castPred]
  all_goals try simp
  all_goals first
    | (rw [δ_D_of_lt q 2 (l n 1) (by simp [Fin.lt_def, l]),
         δ_D_of_lt p 1 (l n 0) (by simp [Fin.lt_def, l])])
    | (rw [δ_D_of_gt p 1 (l n 3) (by simp [Fin.lt_def, l]),
         δ_D_of_gt q 0 (l n 2) (by simp [Fin.lt_def, l])])
    | (rw [hPen_face_const_of_gt h (l n 3) (by simp [Fin.lt_def, l]),
         δ_D_of_gt q 0 (l n 3) (by simp [Fin.lt_def, l])])

private noncomputable def A_fill [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) : (Δ[n + 4] : SSet.{u}) ⟶ X :=
  (A_compatible h).liftOfKanComplex

private noncomputable def A [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  stdSimplex.δ (g n 1) ≫ A_fill h

private lemma A_face_l0 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 0) ≫ A h = SSet.const x := by
  dsimp only [A]
  rw [g1_succ_l0]
  rw [stdSimplex.δ_comp_δ_assoc (i := l n 0) (j := l n 0) (by simp)]
  rw [← g_castSucc_l n 0]
  rw [g_cast0_g0]
  dsimp only [A_fill]
  rw [(A_compatible h).δ_liftOfKanComplex (g n 0) (by simp [g])]
  rw [A_faces_g0]
  apply δ_D_of_lt
  simp [Fin.lt_def, l]

private lemma A_face_l1 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 1) ≫ A h = p.map := by
  dsimp only [A]
  rw [g1_castSucc_l1]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 1) (j := l n 1) (by simp)]
  rw [← g2_succ_l1]
  dsimp only [A_fill]
  rw [(A_compatible h).δ_liftOfKanComplex (g n 2) (by simp [g])]
  rw [A_faces_g2]
  exact δ_D_l1_right p

private lemma A_face_l2 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 2) ≫ A h = r.map := by
  dsimp only [A]
  rw [g1_castSucc_l1]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 1) (j := l n 2) (by simp [l])]
  rw [← g3_succ_l2]
  dsimp only [A_fill]
  rw [(A_compatible h).δ_liftOfKanComplex (g n 3) (by simp [g])]
  rw [A_faces_g3, hPen_face_r]

private lemma A_face_l3 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 3) ≫ A h = q.map := by
  dsimp only [A]
  rw [g1_castSucc_l1]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 1) (j := l n 3) (by simp [l])]
  rw [← g4_succ_l3]
  dsimp only [A_fill]
  rw [(A_compatible h).δ_liftOfKanComplex (g n 4) (by simp [g])]
  rw [A_faces_g4]
  exact δ_D_l1_left q

private lemma A_face_of_lt [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 4)) (hj : j < l n 0) :
    stdSimplex.δ j ≫ A h = SSet.const x := by
  dsimp only [A]
  rw [g1_succ_l0]
  rw [stdSimplex.δ_comp_δ_assoc (i := j) (j := l n 0) hj.le]
  dsimp only [A_fill]
  rw [(A_compatible h).δ_liftOfKanComplex j.castSucc (by
    have hjv : j.val < n := by simpa [Fin.lt_def, l] using hj
    intro hEq
    have heq := congrArg Fin.val hEq
    simp only [Fin.val_castSucc, g_val] at heq
    omega)]
  rw [A_faces_of_lt h j.castSucc (by
    have hjv : j.val < n := by simpa [Fin.lt_def, l] using hj
    simp only [Fin.lt_def, Fin.val_castSucc, g_val]
    omega), comp_const]

private def B_faces (_h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 5)) (_ : j ≠ g n 2) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j = g n 0 then D r 0 else
  if j = g n 1 then D r 0 else
  if j = g n 3 then D p 2 else
  if j = g n 4 then D p 2 else
  SSet.const x

private lemma B_cases (j : Fin (n + 5)) (hj : j ≠ g n 2) :
    j < g n 0 ∨ j = g n 0 ∨ j = g n 1 ∨ j = g n 3 ∨ j = g n 4 := by
  by_cases hpre : j.val < n
  · exact Or.inl hpre
  have hne : j.val ≠ n + 2 := by
    intro h
    apply hj
    apply Fin.ext
    simpa [g] using h
  have hv : j.val = n ∨ j.val = n + 1 ∨ j.val = n + 3 ∨ j.val = n + 4 := by
    have := j.isLt
    omega
  rcases hv with h | h | h | h
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

private lemma lt_g0_ne_g2 {j : Fin (n + 5)} (hj : j < g n 0) :
    j ≠ g n 2 := by
  intro h
  subst j
  simp [Fin.lt_def, g] at hj

private lemma B_faces_of_lt (h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 5)) (hj : j < g n 0) :
    B_faces h j (lt_g0_ne_g2 hj) = SSet.const x := by
  have h0 : j ≠ g n 0 := ne_of_lt hj
  have h1 : j ≠ g n 1 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  have h3 : j ≠ g n 3 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  have h4 : j ≠ g n 4 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  simp [B_faces, h0, h1, h3, h4]

@[simp] private lemma B_faces_g0 (h : MulStruct p q r (Fin.last n).castSucc) :
    B_faces h (g n 0) (by simp [g]) = D r 0 := by simp [B_faces, g]
@[simp] private lemma B_faces_g1 (h : MulStruct p q r (Fin.last n).castSucc) :
    B_faces h (g n 1) (by simp [g]) = D r 0 := by simp [B_faces, g]
@[simp] private lemma B_faces_g3 (h : MulStruct p q r (Fin.last n).castSucc) :
    B_faces h (g n 3) (by simp [g]) = D p 2 := by simp [B_faces, g]
@[simp] private lemma B_faces_g4 (h : MulStruct p q r (Fin.last n).castSucc) :
    B_faces h (g n 4) (by simp [g]) = D p 2 := by simp [B_faces, g]

private lemma B_face_of_prefix (h : MulStruct p q r (Fin.last n).castSucc)
    (j k : Fin (n + 5)) (hj : j < g n 0) (hjk : j < k)
    (hk : k ≠ g n 2) :
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ B_faces h k hk =
      SSet.const x := by
  have hjv : j.val < n := by simpa [Fin.lt_def, g] using hj
  rcases B_cases k hk with hk' | rfl | rfl | rfl | rfl
  · rw [B_faces_of_lt h k hk', comp_const]
  · rw [B_faces_g0]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [B_faces_g1]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [B_faces_g3]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [B_faces_g4]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega

private lemma B_compatible (h : MulStruct p q r (Fin.last n).castSucc) :
    horn.IsCompatible (fun j hj ↦ B_faces h j hj) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  by_cases hj' : j < g n 0
  · rw [B_faces_of_lt h j hj', comp_const]
    exact (B_face_of_prefix h j k hj' hjk hk).symm
  rcases B_cases j hj with hj'' | rfl | rfl | rfl | rfl
  · exact (hj' hj'').elim
  all_goals rcases B_cases k hk with hk' | rfl | rfl | rfl | rfl
  all_goals try { simp only [Fin.lt_def, g_val] at hjk; omega }
  all_goals simp only [B_faces_g0, B_faces_g1, B_faces_g3, B_faces_g4,
    g1_pred, g3_pred, g4_pred, g0_castPred, g1_castPred,
    g3_castPred]
  all_goals first
    | (rw [δ_D_of_gt r 0 (l n 2) (by simp [Fin.lt_def, l]),
         δ_D_of_lt p 2 (l n 0) (by simp [Fin.lt_def, l])])
    | (rw [δ_D_of_gt r 0 (l n 3) (by simp [Fin.lt_def, l]),
         δ_D_of_lt p 2 (l n 0) (by simp [Fin.lt_def, l])])
    | (rw [δ_D_of_gt r 0 (l n 2) (by simp [Fin.lt_def, l]),
         δ_D_of_lt p 2 (l n 1) (by simp [Fin.lt_def, l])])
    | (rw [δ_D_of_gt r 0 (l n 3) (by simp [Fin.lt_def, l]),
         δ_D_of_lt p 2 (l n 1) (by simp [Fin.lt_def, l])])

private noncomputable def B_fill [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) : (Δ[n + 4] : SSet.{u}) ⟶ X :=
  (B_compatible h).liftOfKanComplex

private noncomputable def B [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  stdSimplex.δ (g n 2) ≫ B_fill h

private lemma B_face_l0 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 0) ≫ B h = r.map := by
  dsimp only [B]
  rw [g2_succ_l1]
  rw [stdSimplex.δ_comp_δ_assoc (i := l n 0) (j := l n 1) (by simp [l])]
  rw [← g0_cast_l0]
  dsimp only [B_fill]
  rw [(B_compatible h).δ_liftOfKanComplex (g n 0) (by simp [g])]
  rw [B_faces_g0]
  exact δ_D_l1_left r

private lemma B_face_l1 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 1) ≫ B h = r.map := by
  dsimp only [B]
  rw [g2_succ_l1]
  rw [← stdSimplex.δ_comp_δ_self_assoc (i := l n 1)]
  rw [← g1_cast_l1]
  dsimp only [B_fill]
  rw [(B_compatible h).δ_liftOfKanComplex (g n 1) (by simp [g])]
  rw [B_faces_g1]
  exact δ_D_l1_left r

private lemma B_face_l2 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 2) ≫ B h = p.map := by
  dsimp only [B]
  rw [g2_cast_l2]
  rw [stdSimplex.δ_comp_δ_self_assoc (i := l n 2)]
  rw [← g3_succ_l2]
  dsimp only [B_fill]
  rw [(B_compatible h).δ_liftOfKanComplex (g n 3) (by simp [g])]
  rw [B_faces_g3]
  exact δ_D_l2_right p

private lemma B_face_l3 [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    stdSimplex.δ (l n 3) ≫ B h = p.map := by
  dsimp only [B]
  rw [g2_cast_l2]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 2) (j := l n 3) (by simp [l])]
  rw [← g4_succ_l3]
  dsimp only [B_fill]
  rw [(B_compatible h).δ_liftOfKanComplex (g n 4) (by simp [g])]
  rw [B_faces_g4]
  exact δ_D_l2_right p

private lemma B_face_of_lt [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc)
    (j : Fin (n + 4)) (hj : j < l n 0) :
    stdSimplex.δ j ≫ B h = SSet.const x := by
  dsimp only [B]
  rw [g2_succ_l1]
  rw [stdSimplex.δ_comp_δ_assoc (i := j) (j := l n 1)
    (le_trans hj.le (by simp [l]))]
  dsimp only [B_fill]
  rw [(B_compatible h).δ_liftOfKanComplex j.castSucc (by
    have hjv : j.val < n := by simpa [Fin.lt_def, l] using hj
    intro hEq
    have heq := congrArg Fin.val hEq
    simp only [Fin.val_castSucc, g_val] at heq
    omega)]
  rw [B_faces_of_lt h j.castSucc (by
    have hjv : j.val < n := by simpa [Fin.lt_def, l] using hj
    simp only [Fin.lt_def, Fin.val_castSucc, g_val]
    omega), comp_const]

private def C_faces (h : MulStruct p q rLast (Fin.last (n + 1)))
    (j : Fin (n + 5)) (_ : j ≠ g n 2) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j = g n 0 then D rLast 1 else
  if j = g n 1 then h.map else
  if j = g n 3 then D rLast 0 else
  if j = g n 4 then D p 1 else
  SSet.const x

private lemma C_faces_of_lt (h : MulStruct p q rLast (Fin.last (n + 1)))
    (j : Fin (n + 5)) (hj : j < g n 0) :
    C_faces h j (lt_g0_ne_g2 hj) = SSet.const x := by
  have h0 : j ≠ g n 0 := ne_of_lt hj
  have h1 : j ≠ g n 1 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  have h3 : j ≠ g n 3 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  have h4 : j ≠ g n 4 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  simp [C_faces, h0, h1, h3, h4]

@[simp] private lemma C_faces_g0 (h : MulStruct p q rLast (Fin.last (n + 1))) :
    C_faces h (g n 0) (by simp [g]) = D rLast 1 := by simp [C_faces, g]
@[simp] private lemma C_faces_g1 (h : MulStruct p q rLast (Fin.last (n + 1))) :
    C_faces h (g n 1) (by simp [g]) = h.map := by simp [C_faces, g]
@[simp] private lemma C_faces_g3 (h : MulStruct p q rLast (Fin.last (n + 1))) :
    C_faces h (g n 3) (by simp [g]) = D rLast 0 := by simp [C_faces, g]
@[simp] private lemma C_faces_g4 (h : MulStruct p q rLast (Fin.last (n + 1))) :
    C_faces h (g n 4) (by simp [g]) = D p 1 := by simp [C_faces, g]

private lemma C_face_of_prefix (h : MulStruct p q rLast (Fin.last (n + 1)))
    (j k : Fin (n + 5)) (hj : j < g n 0) (hjk : j < k)
    (hk : k ≠ g n 2) :
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ C_faces h k hk =
      SSet.const x := by
  have hjv : j.val < n := by simpa [Fin.lt_def, g] using hj
  rcases B_cases k hk with hk' | rfl | rfl | rfl | rfl
  · rw [C_faces_of_lt h k hk', comp_const]
  · rw [C_faces_g0]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [C_faces_g1]
    apply hLast_face_const_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [C_faces_g3]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [C_faces_g4]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega

private lemma C_compatible (h : MulStruct p q rLast (Fin.last (n + 1))) :
    horn.IsCompatible (fun j hj ↦ C_faces h j hj) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  by_cases hj' : j < g n 0
  · rw [C_faces_of_lt h j hj', comp_const]
    exact (C_face_of_prefix h j k hj' hjk hk).symm
  rcases B_cases j hj with hj'' | rfl | rfl | rfl | rfl
  · exact (hj' hj'').elim
  all_goals rcases B_cases k hk with hk' | rfl | rfl | rfl | rfl
  all_goals try { simp only [Fin.lt_def, g_val] at hjk; omega }
  all_goals simp only [C_faces_g0, C_faces_g1, C_faces_g3, C_faces_g4,
    g1_pred, g3_pred, g4_pred, g0_castPred, g1_castPred, g3_castPred]
  all_goals try simp [hLast_face_r, hLast_face_p]
  all_goals first
    | (rw [δ_D_of_lt rLast 1 (l n 0) (by simp [Fin.lt_def, l]),
         hLast_face_const_of_lt h (l n 0) (by simp [Fin.lt_def, l])])
    | (rw [δ_D_of_gt rLast 1 (l n 3) (by simp [Fin.lt_def, l]),
         δ_D_of_lt p 1 (l n 0) (by simp [Fin.lt_def, l])])
    | (rw [δ_D_of_gt rLast 0 (l n 3) (by simp [Fin.lt_def, l]),
         δ_D_of_gt p 1 (l n 3) (by simp [Fin.lt_def, l])])

private noncomputable def C_fill [KanComplex X]
    (h : MulStruct p q rLast (Fin.last (n + 1))) : (Δ[n + 4] : SSet.{u}) ⟶ X :=
  (C_compatible h).liftOfKanComplex

private noncomputable def C [KanComplex X]
    (h : MulStruct p q rLast (Fin.last (n + 1))) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  stdSimplex.δ (g n 2) ≫ C_fill h

private lemma C_face_l0 [KanComplex X]
    (h : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 0) ≫ C h = rLast.map := by
  dsimp only [C]
  rw [g2_succ_l1]
  rw [stdSimplex.δ_comp_δ_assoc (i := l n 0) (j := l n 1) (by simp [l])]
  rw [← g0_cast_l0]
  dsimp only [C_fill]
  rw [(C_compatible h).δ_liftOfKanComplex (g n 0) (by simp [g])]
  rw [C_faces_g0]
  exact δ_D_l1_right rLast

private lemma C_face_l1 [KanComplex X]
    (h : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 1) ≫ C h = q.map := by
  dsimp only [C]
  rw [g2_succ_l1]
  rw [← stdSimplex.δ_comp_δ_self_assoc (i := l n 1)]
  rw [← g1_cast_l1]
  dsimp only [C_fill]
  rw [(C_compatible h).δ_liftOfKanComplex (g n 1) (by simp [g])]
  rw [C_faces_g1, hLast_face_q]

private lemma C_face_l2 [KanComplex X]
    (h : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 2) ≫ C h = SSet.const x := by
  dsimp only [C]
  rw [g2_cast_l2]
  rw [stdSimplex.δ_comp_δ_self_assoc (i := l n 2)]
  rw [← g3_succ_l2]
  dsimp only [C_fill]
  rw [(C_compatible h).δ_liftOfKanComplex (g n 3) (by simp [g])]
  rw [C_faces_g3]
  apply δ_D_of_gt
  simp [Fin.lt_def, l]

private lemma C_face_l3 [KanComplex X]
    (h : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 3) ≫ C h = p.map := by
  dsimp only [C]
  rw [g2_cast_l2]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 2) (j := l n 3) (by simp [l])]
  rw [← g4_succ_l3]
  dsimp only [C_fill]
  rw [(C_compatible h).δ_liftOfKanComplex (g n 4) (by simp [g])]
  rw [C_faces_g4]
  exact δ_D_l2_left p

private lemma C_face_of_lt [KanComplex X]
    (h : MulStruct p q rLast (Fin.last (n + 1)))
    (j : Fin (n + 4)) (hj : j < l n 0) :
    stdSimplex.δ j ≫ C h = SSet.const x := by
  dsimp only [C]
  rw [g2_succ_l1]
  rw [stdSimplex.δ_comp_δ_assoc (i := j) (j := l n 1)
    (le_trans hj.le (by simp [l]))]
  dsimp only [C_fill]
  rw [(C_compatible h).δ_liftOfKanComplex j.castSucc (by
    have hjv : j.val < n := by simpa [Fin.lt_def, l] using hj
    intro hEq
    have heq := congrArg Fin.val hEq
    simp only [Fin.val_castSucc, g_val] at heq
    omega)]
  rw [C_faces_of_lt h j.castSucc (by
    have hjv : j.val < n := by simpa [Fin.lt_def, l] using hj
    simp only [Fin.lt_def, Fin.val_castSucc, g_val]
    omega), comp_const]

private noncomputable def R_faces [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1)))
    (j : Fin (n + 5)) (_ : j ≠ g n 0) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j = g n 1 then A h₀ else
  if j = g n 2 then D p 1 else
  if j = g n 3 then B h₀ else
  if j = g n 4 then C h₁ else
  SSet.const x

private lemma R_cases (j : Fin (n + 5)) (hj : j ≠ g n 0) :
    j < g n 0 ∨ j = g n 1 ∨ j = g n 2 ∨ j = g n 3 ∨ j = g n 4 := by
  by_cases hpre : j.val < n
  · exact Or.inl hpre
  have hne : j.val ≠ n := by
    intro h
    apply hj
    apply Fin.ext
    simpa [g] using h
  have hv : j.val = n + 1 ∨ j.val = n + 2 ∨ j.val = n + 3 ∨ j.val = n + 4 := by
    have := j.isLt
    omega
  rcases hv with h | h | h | h
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

private lemma R_faces_of_lt [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1)))
    (j : Fin (n + 5)) (hj : j < g n 0) :
    R_faces h₀ h₁ j (ne_of_lt hj) = SSet.const x := by
  have h1 : j ≠ g n 1 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  have h2 : j ≠ g n 2 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  have h3 : j ≠ g n 3 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  have h4 : j ≠ g n 4 := by intro e; subst j; simp [Fin.lt_def, g] at hj
  simp [R_faces, h1, h2, h3, h4]

@[simp] private lemma R_faces_g1 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    R_faces h₀ h₁ (g n 1) (by simp [g]) = A h₀ := by simp [R_faces, g]
@[simp] private lemma R_faces_g2 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    R_faces h₀ h₁ (g n 2) (by simp [g]) = D p 1 := by simp [R_faces, g]
@[simp] private lemma R_faces_g3 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    R_faces h₀ h₁ (g n 3) (by simp [g]) = B h₀ := by simp [R_faces, g]
@[simp] private lemma R_faces_g4 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    R_faces h₀ h₁ (g n 4) (by simp [g]) = C h₁ := by simp [R_faces, g]

private lemma R_face_of_prefix [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1)))
    (j k : Fin (n + 5)) (hj : j < g n 0) (hjk : j < k)
    (hk : k ≠ g n 0) :
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ R_faces h₀ h₁ k hk =
      SSet.const x := by
  have hjv : j.val < n := by simpa [Fin.lt_def, g] using hj
  rcases R_cases k hk with hk' | rfl | rfl | rfl | rfl
  · rw [R_faces_of_lt h₀ h₁ k hk', comp_const]
  · rw [R_faces_g1]
    apply A_face_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [R_faces_g2]
    apply δ_D_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [R_faces_g3]
    apply B_face_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega
  · rw [R_faces_g4]
    apply C_face_of_lt
    simp only [Fin.lt_def, Fin.coe_castPred, l_val]
    omega

private lemma R_compatible [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    horn.IsCompatible (fun j hj ↦ R_faces h₀ h₁ j hj) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  by_cases hj' : j < g n 0
  · rw [R_faces_of_lt h₀ h₁ j hj', comp_const]
    exact (R_face_of_prefix h₀ h₁ j k hj' hjk hk).symm
  rcases R_cases j hj with hj'' | rfl | rfl | rfl | rfl
  · exact (hj' hj'').elim
  all_goals rcases R_cases k hk with hk' | rfl | rfl | rfl | rfl
  all_goals try { simp only [Fin.lt_def, g_val] at hjk; omega }
  all_goals simp only [R_faces_g1, R_faces_g2, R_faces_g3, R_faces_g4,
    g2_pred, g3_pred, g4_pred, g1_castPred, g2_castPred, g3_castPred]
  all_goals try simp only [A_face_l1, A_face_l2, A_face_l3, B_face_l1, B_face_l2,
    B_face_l3, C_face_l1, C_face_l2, C_face_l3, δ_D_l1_right,
    δ_D_l2_left]
  all_goals rw [δ_D_of_gt p 1 (l n 3) (by simp [Fin.lt_def, l])]

private noncomputable def R_fill [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    (Δ[n + 4] : SSet.{u}) ⟶ X :=
  (R_compatible h₀ h₁).liftOfKanComplex

private noncomputable def R [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    (Δ[n + 3] : SSet.{u}) ⟶ X :=
  stdSimplex.δ (g n 0) ≫ R_fill h₀ h₁

private lemma R_face_l0 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 0) ≫ R h₀ h₁ = SSet.const x := by
  dsimp only [R]
  rw [g0_cast_l0]
  rw [stdSimplex.δ_comp_δ_self_assoc (i := l n 0)]
  rw [← g1_succ_l0]
  dsimp only [R_fill]
  rw [(R_compatible h₀ h₁).δ_liftOfKanComplex (g n 1) (by simp [g])]
  rw [R_faces_g1, A_face_l0]

private lemma R_face_l1 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 1) ≫ R h₀ h₁ = SSet.const x := by
  dsimp only [R]
  rw [g0_cast_l0]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 0) (j := l n 1) (by simp [l])]
  rw [← g2_succ_l1]
  dsimp only [R_fill]
  rw [(R_compatible h₀ h₁).δ_liftOfKanComplex (g n 2) (by simp [g])]
  rw [R_faces_g2]
  apply δ_D_of_lt
  simp [Fin.lt_def, l]

private lemma R_face_l2 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 2) ≫ R h₀ h₁ = r.map := by
  dsimp only [R]
  rw [g0_cast_l0]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 0) (j := l n 2) (by simp [l])]
  rw [← g3_succ_l2]
  dsimp only [R_fill]
  rw [(R_compatible h₀ h₁).δ_liftOfKanComplex (g n 3) (by simp [g])]
  rw [R_faces_g3, B_face_l0]

private lemma R_face_l3 [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    stdSimplex.δ (l n 3) ≫ R h₀ h₁ = rLast.map := by
  dsimp only [R]
  rw [g0_cast_l0]
  rw [← stdSimplex.δ_comp_δ_assoc (i := l n 0) (j := l n 3) (by simp [l])]
  rw [← g4_succ_l3]
  dsimp only [R_fill]
  rw [(R_compatible h₀ h₁).δ_liftOfKanComplex (g n 4) (by simp [g])]
  rw [R_faces_g4, C_face_l0]

private lemma R_face_of_lt [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1)))
    (j : Fin (n + 4)) (hj : j < l n 0) :
    stdSimplex.δ j ≫ R h₀ h₁ = SSet.const x := by
  have hjv : j.val < n := by simpa [Fin.lt_def, l] using hj
  have hg0 : g n 0 ≠ 0 := by
    intro hEq
    have heq := congrArg Fin.val hEq
    simp [g] at heq
    omega
  let k : Fin (n + 4) := (g n 0).pred hg0
  have hk : j ≤ k := by
    change j.val ≤ (g n 0).val - 1
    simp only [g_val]
    omega
  dsimp only [R]
  rw [← Fin.succ_pred (g n 0) hg0]
  rw [stdSimplex.δ_comp_δ_assoc (i := j) (j := k) hk]
  dsimp only [R_fill]
  have hjg : j.castSucc < g n 0 := by
    simp only [Fin.lt_def, Fin.val_castSucc, g_val]
    omega
  rw [(R_compatible h₀ h₁).δ_liftOfKanComplex j.castSucc hjg.ne]
  rw [R_faces_of_lt h₀ h₁ j.castSucc hjg, comp_const]

private lemma l_rel_castSucc (n : ℕ) :
    l n 2 = (Fin.last (n + 2)).castSucc := by
  apply Fin.ext
  simp [l]

private lemma l_rel_succ (n : ℕ) :
    l n 3 = (Fin.last (n + 2)).succ := by
  apply Fin.ext
  simp [l]

private noncomputable def adjacentRelStruct₀ [KanComplex X]
    (h₀ : MulStruct p q r (Fin.last n).castSucc)
    (h₁ : MulStruct p q rLast (Fin.last (n + 1))) :
    r.RelStruct₀ rLast :=
  (show r.RelStruct rLast (Fin.last (n + 2)) from
    { map := R h₀ h₁
      δ_castSucc_map := by rw [← l_rel_castSucc, R_face_l2]
      δ_succ_map := by rw [← l_rel_succ, R_face_l3]
      δ_map_of_lt := by
        intro j hj
        have hjv : j.val < n + 2 := by
          change j.val < (Fin.last (n + 2)).castSucc.val at hj
          simpa using hj
        by_cases hpre : j.val < n
        · apply R_face_of_lt h₀ h₁ j
          simpa [Fin.lt_def, l] using hpre
        · have hv : j.val = n ∨ j.val = n + 1 := by omega
          rcases hv with hv | hv
          · rw [show j = l n 0 by apply Fin.ext; simpa [l] using hv]
            exact R_face_l0 h₀ h₁
          · rw [show j = l n 1 by apply Fin.ext; simpa [l] using hv]
            exact R_face_l1 h₀ h₁
      δ_map_of_gt := by
        intro j hj
        exact (not_lt_of_ge (Fin.le_last j) hj).elim }).relStruct₀

/-- Let X be a Kan simplicial set in universe u, x∈X₀ and n∈ℕ. If pointed (n+2)-simplices p,q,r
admit a multiplication structure at index Fin.castSucc(Fin.last n), then [p]·[q]=[r] in
π_{n+2}(X,x). This agrees with the group multiplication chosen at index Fin.last(n+1), so the
statement includes every degree at least two. -/
theorem mul_eq_penultimate [KanComplex X]
    (h : MulStruct p q r (Fin.last n).castSucc) :
    KanComplex.π.mk p * KanComplex.π.mk q = KanComplex.π.mk r := by
  obtain ⟨rLast, ⟨hLast⟩⟩ := MulStruct.nonempty p q (Fin.last (n + 1))
  exact hLast.mul_eq.trans
    ((KanComplex.π.mk_eq_mk_iff.2 ⟨adjacentRelStruct₀ h hLast⟩).symm)

end SSet.PtSimplex.MulStruct
