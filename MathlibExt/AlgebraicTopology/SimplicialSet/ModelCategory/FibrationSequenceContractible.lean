/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroupIndex
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid

/-!
# Connecting maps with subsingleton total homotopy groups

Let S be a pointed simplicial fibration p:E→B in universe u, with Kan base B, points e,b
satisfying p(e)=b, and strict fiber F over b. Its connecting map is δ_n:π_{n+1}(B,b)→π_n(F,e).

For positive target degree, δ_{n+1} preserves multiplication. If two base loops have equal δ₀
images, they differ on the right by the image of a total-space loop. If every π_n(E,e),
including n=0, is subsingleton, each δ_n is bijective.
-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FibrationSequence

private theorem mk_const_eq_inv_mul {X : SSet.{u}} [KanComplex X]
    (x : X _⦋0⦌) (n : ℕ) (p : KanComplex.π (n + 1) X x) :
    KanComplex.π.mk (RelativeMorphism.const : X.PtSimplex (n + 1) x) =
      p⁻¹ * p := by
  let q := KanComplex.π.mk
    (RelativeMorphism.const : X.PtSimplex (n + 1) x)
  have hq : q * q = q := PtSimplex.MulStruct.mul_eq
    (PtSimplex.MulStruct.mulOne
      (RelativeMorphism.const : X.PtSimplex (n + 1) x) (Fin.last n))
  calc
    q = q⁻¹ * (q * q) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ = q⁻¹ * q := by rw [hq]
    _ = p⁻¹ * p := by rw [inv_mul_cancel, inv_mul_cancel]

private def edgeOfPtSimplexOne {X : SSet.{u}} {x : X _⦋0⦌}
    (s : X.PtSimplex 1 x) : Edge x x :=
  Edge.mk (SSet.yonedaEquiv (RelativeMorphism.map s))
    (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp,
      SSet.yonedaEquiv_const])
    (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp,
      SSet.yonedaEquiv_const])

private def ptSimplexOneOfLoopEdge {X : SSet.{u}} {x : X _⦋0⦌}
    (e : Edge x x) : X.PtSimplex 1 x where
  map := SSet.yonedaEquiv.symm e.edge
  comm := by
    apply SSet.boundary.hom_ext
    intro i
    fin_cases i <;>
      simp [SSet.boundary.ι_ι_assoc,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm]

@[simp]
private theorem ptSimplexOneOfLoopEdge_edgeOfPtSimplexOne
    {X : SSet.{u}} {x : X _⦋0⦌} (s : X.PtSimplex 1 x) :
    ptSimplexOneOfLoopEdge (edgeOfPtSimplexOne s) = s := by
  apply RelativeMorphism.ext
  simp [ptSimplexOneOfLoopEdge, edgeOfPtSimplexOne]

private theorem mul_mk_eq_of_compStruct {X : SSet.{u}} [KanComplex X]
    {x : X _⦋0⦌} {e₀₁ e₁₂ e₀₂ : Edge x x}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    KanComplex.π.mk (ptSimplexOneOfLoopEdge e₀₁) *
        KanComplex.π.mk (ptSimplexOneOfLoopEdge e₁₂) =
      KanComplex.π.mk (ptSimplexOneOfLoopEdge e₀₂) := by
  apply PtSimplex.MulStruct.mul_eq
  exact
    { map := SSet.yonedaEquiv.symm h.simplex
      δ_castSucc_castSucc_map := by
        apply SSet.yonedaEquiv.injective
        simp [ptSimplexOneOfLoopEdge]
      δ_succ_castSucc_map := by
        apply SSet.yonedaEquiv.injective
        simp [ptSimplexOneOfLoopEdge]
      δ_succ_succ_map := by
        apply SSet.yonedaEquiv.injective
        simp [ptSimplexOneOfLoopEdge]
      δ_map_of_lt := by grind
      δ_map_of_gt := by grind }

private noncomputable def chosenLiftEdge (S : FibrationSequence.{u})
    [Fibration S.p] (s : S.B.PtSimplex 1 S.b) :
    Edge
      (PtSimplex.equiv₀ S.e
        (ConnectingMap.chosenLiftPt
          (e := S.e) (b := S.b) S.p S.hb s))
      S.e := by
  let lift := ConnectingMap.chosenLift
    (e := S.e) (b := S.b) S.p S.hb s
  let pt := ConnectingMap.chosenLiftPt
    (e := S.e) (b := S.b) S.p S.hb s
  refine Edge.mk lift ?_ ?_
  · apply SSet.yonedaEquiv.symm.injective
    calc
      SSet.yonedaEquiv.symm (S.E.δ 1 lift) =
          SSet.stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm lift :=
        (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).symm
      _ = RelativeMorphism.map pt :=
        (ConnectingMap.chosenLift_face_eq
          (e := S.e) (b := S.b) S.p S.hb s).symm
      _ = SSet.const (PtSimplex.equiv₀ S.e pt) :=
        PtSimplex.map_eq_const_equiv₀ pt
      _ = SSet.yonedaEquiv.symm (PtSimplex.equiv₀ S.e pt) :=
        (SSet.yonedaEquiv_symm_zero _).symm
  · apply SSet.yonedaEquiv.symm.injective
    calc
      SSet.yonedaEquiv.symm (S.E.δ 0 lift) =
          SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm lift :=
        (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).symm
      _ = SSet.const S.e :=
        ConnectingMap.chosenLift_face_eq_const
          (e := S.e) (b := S.b) S.p S.hb s (0 : Fin 2) (by decide)
      _ = SSet.yonedaEquiv.symm S.e :=
        (SSet.yonedaEquiv_symm_zero S.e).symm

private theorem connectingVertex_fiberIncl (S : FibrationSequence.{u})
    [Fibration S.p] (s : S.B.PtSimplex 1 S.b) :
    S.fiberIncl.app _
        (PtSimplex.equiv₀ S.fiberPoint
          (ConnectingMap.connectingPtSimplexRep
            (p := S.p) (e := S.e) S.hb s)) =
      PtSimplex.equiv₀ S.e
        (ConnectingMap.chosenLiftPt
          (e := S.e) (b := S.b) S.p S.hb s) := by
  let r := ConnectingMap.connectingPtSimplexRep
    (p := S.p) (e := S.e) S.hb s
  let t := ConnectingMap.chosenLiftPt
    (e := S.e) (b := S.b) S.p S.hb s
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.yonedaEquiv_symm_zero, SSet.yonedaEquiv_symm_zero]
  change SSet.const
      (S.fiberIncl.app _ (PtSimplex.equiv₀ S.fiberPoint r)) =
    SSet.const (PtSimplex.equiv₀ S.e t)
  calc
    SSet.const (S.fiberIncl.app _ (PtSimplex.equiv₀ S.fiberPoint r)) =
        SSet.const (PtSimplex.equiv₀ S.fiberPoint r) ≫ S.fiberIncl := by
      rw [SSet.const_comp]
    _ = RelativeMorphism.map r ≫ S.fiberIncl := by
      rw [PtSimplex.map_eq_const_equiv₀]
    _ = RelativeMorphism.map t := by
      simpa [r, t] using
        (ConnectingMap.connectingPtSimplexRep_ι
          (p := S.p) (e := S.e) S.hb s)
    _ = SSet.const (PtSimplex.equiv₀ S.e t) :=
      PtSimplex.map_eq_const_equiv₀ t

private theorem chosenLiftEdge_map_p (S : FibrationSequence.{u})
    [Fibration S.p] (s : S.B.PtSimplex 1 S.b)
    (hsrc : S.p.app _
        (PtSimplex.equiv₀ S.e
          (ConnectingMap.chosenLiftPt
            (e := S.e) (b := S.b) S.p S.hb s)) = S.b) :
    ((chosenLiftEdge S s).map S.p).ofEq hsrc S.hb =
      edgeOfPtSimplexOne s := by
  apply Edge.ext
  change ((chosenLiftEdge S s).map S.p).edge =
    (edgeOfPtSimplexOne s).edge
  rw [Edge.map_edge]
  change S.p.app _
      (ConnectingMap.chosenLift
        (e := S.e) (b := S.b) S.p S.hb s) =
    SSet.yonedaEquiv (RelativeMorphism.map s)
  apply SSet.yonedaEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  rw [← SSet.yonedaEquiv_symm_comp]
  exact ConnectingMap.chosenLift_projects
    (e := S.e) (b := S.b) S.p S.hb s

private theorem chosenLiftVertex_p (S : FibrationSequence.{u})
    [Fibration S.p] (s : S.B.PtSimplex 1 S.b) :
    S.p.app _
        (PtSimplex.equiv₀ S.e
          (ConnectingMap.chosenLiftPt
            (e := S.e) (b := S.b) S.p S.hb s)) = S.b := by
  let t := ConnectingMap.chosenLiftPt
    (e := S.e) (b := S.b) S.p S.hb s
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.yonedaEquiv_symm_zero, SSet.yonedaEquiv_symm_zero]
  calc
    SSet.const (S.p.app _ (PtSimplex.equiv₀ S.e t)) =
        SSet.const (PtSimplex.equiv₀ S.e t) ≫ S.p := by
      rw [SSet.const_comp]
    _ = RelativeMorphism.map t ≫ S.p := by
      rw [PtSimplex.map_eq_const_equiv₀]
    _ = SSet.const S.b := by
      simpa [t] using
        (ConnectingMap.pt_map_comp_const
          (e := S.e) (b := S.b) S.p S.hb s)

/-!
## Multiplication in positive target degree

For n≥0, δ_{n+1}:π_{n+2}(B,b)→π_{n+1}(F,e) is multiplicative. Degree-zero connecting images
instead control the right action of loops lifted from the total space.
-/

private def mulGlobalIndex (n : ℕ) (t : Fin 3) : Fin (n + 4) :=
  ⟨n + t, by omega⟩

private def mulLocalIndex (n : ℕ) (t : Fin 3) : Fin (n + 3) :=
  ⟨n + t, by omega⟩

@[simp]
private lemma mulGlobalIndex_val (n : ℕ) (t : Fin 3) :
    (mulGlobalIndex n t).val = n + t := rfl

@[simp]
private lemma mulLocalIndex_val (n : ℕ) (t : Fin 3) :
    (mulLocalIndex n t).val = n + t := rfl

private lemma mulLocalIndex_castSucc (n : ℕ) (t : Fin 3) :
    (mulLocalIndex n t).castSucc = mulGlobalIndex n t := by
  apply Fin.ext
  simp [mulLocalIndex, mulGlobalIndex]

private lemma mulGlobalIndex_ne_last (n : ℕ) (t : Fin 3) :
    mulGlobalIndex n t ≠ Fin.last (n + 3) := by
  intro h
  have hv := congrArg Fin.val h
  simp [mulGlobalIndex] at hv
  omega

private lemma mulGlobalIndex_zero_eq (n : ℕ) :
    mulGlobalIndex n 0 =
      (Fin.last n).castSucc.castSucc.castSucc := by
  apply Fin.ext
  simp [mulGlobalIndex]

private lemma mulGlobalIndex_one_eq (n : ℕ) :
    mulGlobalIndex n 1 =
      (Fin.last n).castSucc.castSucc.succ := by
  apply Fin.ext
  simp [mulGlobalIndex]

private lemma mulGlobalIndex_two_eq (n : ℕ) :
    mulGlobalIndex n 2 =
      (Fin.last n).castSucc.succ.succ := by
  apply Fin.ext
  simp [mulGlobalIndex]

private lemma mulLocalIndex_zero_eq (n : ℕ) :
    mulLocalIndex n 0 = (Fin.last n).castSucc.castSucc := by
  apply Fin.ext
  simp [mulLocalIndex]

private lemma mulLocalIndex_one_eq (n : ℕ) :
    mulLocalIndex n 1 = (Fin.last n).castSucc.succ := by
  apply Fin.ext
  simp [mulLocalIndex]

private lemma mulLocalIndex_two_eq (n : ℕ) :
    mulLocalIndex n 2 = (Fin.last n).succ.succ := by
  apply Fin.ext
  simp [mulLocalIndex]

private lemma mulGlobalIndex_cases (n : ℕ) (j : Fin (n + 4))
    (hj : j ≠ Fin.last (n + 3)) :
    j < mulGlobalIndex n 0 ∨
      j = mulGlobalIndex n 0 ∨
      j = mulGlobalIndex n 1 ∨
      j = mulGlobalIndex n 2 := by
  by_cases hpre : j.val < n
  · exact Or.inl hpre
  have hlast : j.val ≠ n + 3 := by
    intro h
    apply hj
    apply Fin.ext
    simpa using h
  have hv : j.val = n ∨ j.val = n + 1 ∨ j.val = n + 2 := by
    have := j.isLt
    omega
  rcases hv with h | h | h
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

private lemma chosenLift_face_const (S : FibrationSequence.{u})
    [Fibration S.p] {n : ℕ} (σ : S.B.PtSimplex (n + 2) S.b)
    (j : Fin (n + 3)) (hj : j < Fin.last (n + 2)) :
    stdSimplex.δ j ≫ SSet.yonedaEquiv.symm
        (ConnectingMap.chosenLift
          (e := S.e) (b := S.b) S.p S.hb σ) =
      SSet.const (X := Δ[n + 1]) S.e :=
  ConnectingMap.chosenLift_face_eq_const
    (e := S.e) (b := S.b) S.p S.hb σ j (ne_of_lt hj)

private noncomputable def connectingMulFaces
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    (σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b)
    (j : Fin (n + 4)) (_ : j ≠ Fin.last (n + 3)) :
    (Δ[n + 2] : SSet.{u}) ⟶ S.E :=
  if j = mulGlobalIndex n 0 then
    SSet.yonedaEquiv.symm
      (ConnectingMap.chosenLift
        (e := S.e) (b := S.b) S.p S.hb σ₂)
  else if j = mulGlobalIndex n 1 then
    SSet.yonedaEquiv.symm
      (ConnectingMap.chosenLift
        (e := S.e) (b := S.b) S.p S.hb σ₁₂)
  else if j = mulGlobalIndex n 2 then
    SSet.yonedaEquiv.symm
      (ConnectingMap.chosenLift
        (e := S.e) (b := S.b) S.p S.hb σ₁)
  else
    SSet.const S.e

private lemma connectingMulFaces_of_lt
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    (σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b)
    (j : Fin (n + 4)) (hj : j < mulGlobalIndex n 0) :
    connectingMulFaces S σ₁ σ₂ σ₁₂ j (by
      intro h
      subst j
      simp [Fin.lt_def, mulGlobalIndex] at hj) =
      SSet.const S.e := by
  have h0 : j ≠ mulGlobalIndex n 0 := ne_of_lt hj
  have h1 : j ≠ mulGlobalIndex n 1 := by
    intro h
    subst j
    simp [Fin.lt_def, mulGlobalIndex] at hj
  have h2 : j ≠ mulGlobalIndex n 2 := by
    intro h
    subst j
    simp [Fin.lt_def, mulGlobalIndex] at hj
  simp [connectingMulFaces, h0, h1, h2]

@[simp]
private lemma connectingMulFaces_zero
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    (σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b) :
    connectingMulFaces S σ₁ σ₂ σ₁₂ (mulGlobalIndex n 0)
      (mulGlobalIndex_ne_last n 0) =
      SSet.yonedaEquiv.symm
        (ConnectingMap.chosenLift
          (e := S.e) (b := S.b) S.p S.hb σ₂) := by
  simp [connectingMulFaces, mulGlobalIndex]

@[simp]
private lemma connectingMulFaces_one
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    (σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b) :
    connectingMulFaces S σ₁ σ₂ σ₁₂ (mulGlobalIndex n 1)
      (mulGlobalIndex_ne_last n 1) =
      SSet.yonedaEquiv.symm
        (ConnectingMap.chosenLift
          (e := S.e) (b := S.b) S.p S.hb σ₁₂) := by
  simp [connectingMulFaces, mulGlobalIndex]

@[simp]
private lemma connectingMulFaces_two
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    (σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b) :
    connectingMulFaces S σ₁ σ₂ σ₁₂ (mulGlobalIndex n 2)
      (mulGlobalIndex_ne_last n 2) =
      SSet.yonedaEquiv.symm
        (ConnectingMap.chosenLift
          (e := S.e) (b := S.b) S.p S.hb σ₁) := by
  simp [connectingMulFaces, mulGlobalIndex]

private lemma connectingMulFaces_face_of_prefix
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    (σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b)
    (j k : Fin (n + 4)) (hj : j < mulGlobalIndex n 0)
    (hjk : j < k) (hk : k ≠ Fin.last (n + 3)) :
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫
        connectingMulFaces S σ₁ σ₂ σ₁₂ k hk =
      SSet.const S.e := by
  have hjv : j.val < n := by
    simpa [Fin.lt_def, mulGlobalIndex] using hj
  rcases mulGlobalIndex_cases n k hk with hk' | rfl | rfl | rfl
  · rw [connectingMulFaces_of_lt S σ₁ σ₂ σ₁₂ k hk',
      SSet.comp_const]
  · rw [connectingMulFaces_zero]
    apply chosenLift_face_const
    simp only [Fin.lt_def, Fin.coe_castPred, Fin.val_last]
    omega
  · rw [connectingMulFaces_one]
    apply chosenLift_face_const
    simp only [Fin.lt_def, Fin.coe_castPred, Fin.val_last]
    omega
  · rw [connectingMulFaces_two]
    apply chosenLift_face_const
    simp only [Fin.lt_def, Fin.coe_castPred, Fin.val_last]
    omega

private lemma connectingMulFaces_compatible
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    (σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b) :
    horn.IsCompatible
      (fun j hj ↦ connectingMulFaces S σ₁ σ₂ σ₁₂ j hj) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  by_cases hj' : j < mulGlobalIndex n 0
  · rw [connectingMulFaces_of_lt S σ₁ σ₂ σ₁₂ j hj',
      SSet.comp_const]
    exact (connectingMulFaces_face_of_prefix
      S σ₁ σ₂ σ₁₂ j k hj' hjk hk).symm
  rcases mulGlobalIndex_cases n j hj with hj'' | rfl | rfl | rfl
  · exact (hj' hj'').elim
  all_goals
    rcases mulGlobalIndex_cases n k hk with hk' | rfl | rfl | rfl
  all_goals
    try
      { simp only [Fin.lt_def, mulGlobalIndex_val] at hjk
        omega }
  all_goals
    simp only [connectingMulFaces_zero, connectingMulFaces_one,
      connectingMulFaces_two]
  all_goals
    rw [chosenLift_face_const S, chosenLift_face_const S]
  all_goals
    simp only [Fin.lt_def, Fin.val_pred, Fin.coe_castPred, Fin.val_last,
      mulGlobalIndex_val]
  all_goals omega

private lemma connectingMulFaces_comp
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc)
    (j : Fin (n + 4)) (hj : j ≠ Fin.last (n + 3)) :
    connectingMulFaces S σ₁ σ₂ σ₁₂ j hj ≫ S.p =
      stdSimplex.δ j ≫ hBase.map := by
  rcases mulGlobalIndex_cases n j hj with hj' | rfl | rfl | rfl
  · rw [connectingMulFaces_of_lt S σ₁ σ₂ σ₁₂ j hj',
      SSet.const_comp, S.hb]
    apply (hBase.δ_map_of_lt j ?_).symm
    rw [← mulGlobalIndex_zero_eq]
    exact hj'
  · rw [connectingMulFaces_zero,
      ConnectingMap.chosenLift_projects,
      mulGlobalIndex_zero_eq,
      hBase.δ_castSucc_castSucc_map]
  · rw [connectingMulFaces_one,
      ConnectingMap.chosenLift_projects,
      mulGlobalIndex_one_eq,
      hBase.δ_succ_castSucc_map]
  · rw [connectingMulFaces_two,
      ConnectingMap.chosenLift_projects,
      mulGlobalIndex_two_eq,
      hBase.δ_succ_succ_map]

private noncomputable def connectingMulLift
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    (Δ[n + 3] : SSet.{u}) ⟶ S.E :=
  (connectingMulFaces_compatible S σ₁ σ₂ σ₁₂).lift
    S.p hBase.map (connectingMulFaces_comp S hBase)

@[reassoc]
private lemma connectingMulLift_comp
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    connectingMulLift S hBase ≫ S.p = hBase.map :=
  (connectingMulFaces_compatible S σ₁ σ₂ σ₁₂).lift_comp
    S.p hBase.map (connectingMulFaces_comp S hBase)

@[reassoc]
private lemma connectingMulLift_face
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc)
    (j : Fin (n + 4)) (hj : j ≠ Fin.last (n + 3)) :
    stdSimplex.δ j ≫ connectingMulLift S hBase =
      connectingMulFaces S σ₁ σ₂ σ₁₂ j hj :=
  (connectingMulFaces_compatible S σ₁ σ₂ σ₁₂).δ_lift
    S.p hBase.map (connectingMulFaces_comp S hBase) j hj

private noncomputable def connectingMulFinalFace
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    (Δ[n + 2] : SSet.{u}) ⟶ S.E :=
  stdSimplex.δ (Fin.last (n + 3)) ≫ connectingMulLift S hBase

private lemma connectingMulFinalFace_comp
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    connectingMulFinalFace S hBase ≫ S.p =
      SSet.const S.b := by
  dsimp only [connectingMulFinalFace]
  rw [Category.assoc, connectingMulLift_comp]
  apply hBase.δ_map_of_gt
  simp [Fin.lt_def]

private noncomputable def connectingMulFiberMap
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    (Δ[n + 2] : SSet.{u}) ⟶ S.fiber :=
  Subcomplex.lift (connectingMulFinalFace S hBase) (by
    rw [Subcomplex.range_le_fiber_iff]
    exact connectingMulFinalFace_comp S hBase)

@[reassoc]
private lemma connectingMulFiberMap_ι
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    connectingMulFiberMap S hBase ≫ S.fiberIncl =
      connectingMulFinalFace S hBase := by
  dsimp only [connectingMulFiberMap]
  rw [Subcomplex.lift_ι]

private lemma connectingMulFiberMap_face
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc)
    (t : Fin 3) (σ : S.B.PtSimplex (n + 2) S.b)
    (hFace :
      connectingMulFaces S σ₁ σ₂ σ₁₂ (mulGlobalIndex n t)
          (mulGlobalIndex_ne_last n t) =
        SSet.yonedaEquiv.symm
          (ConnectingMap.chosenLift
            (e := S.e) (b := S.b) S.p S.hb σ)) :
    stdSimplex.δ (mulLocalIndex n t) ≫
        connectingMulFiberMap S hBase =
      RelativeMorphism.map
        (ConnectingMap.connectingPtSimplexRep
          (p := S.p) (e := S.e) S.hb σ) := by
  apply (cancel_mono S.fiberIncl).mp
  calc
    (stdSimplex.δ (mulLocalIndex n t) ≫
        connectingMulFiberMap S hBase) ≫ S.fiberIncl =
      stdSimplex.δ (mulLocalIndex n t) ≫
        (connectingMulFiberMap S hBase ≫ S.fiberIncl) := by
          rw [Category.assoc]
    _ = stdSimplex.δ (mulLocalIndex n t) ≫
        connectingMulFinalFace S hBase := by
          rw [connectingMulFiberMap_ι]
    _ = (stdSimplex.δ (mulLocalIndex n t) ≫
          stdSimplex.δ (Fin.last (n + 3))) ≫
        connectingMulLift S hBase := by
          rfl
    _ = (stdSimplex.δ (Fin.last (n + 2)) ≫
          stdSimplex.δ (mulLocalIndex n t).castSucc) ≫
        connectingMulLift S hBase := by
          rw [show Fin.last (n + 3) =
            (Fin.last (n + 2)).succ by rfl]
          simp only [Category.assoc]
          rw [stdSimplex.δ_comp_δ_assoc (Fin.le_last _)]
    _ = stdSimplex.δ (Fin.last (n + 2)) ≫
        (stdSimplex.δ (mulGlobalIndex n t) ≫
          connectingMulLift S hBase) := by
          rw [mulLocalIndex_castSucc, Category.assoc]
    _ = stdSimplex.δ (Fin.last (n + 2)) ≫
        connectingMulFaces S σ₁ σ₂ σ₁₂ (mulGlobalIndex n t)
          (mulGlobalIndex_ne_last n t) := by
            rw [connectingMulLift_face]
    _ = stdSimplex.δ (Fin.last (n + 2)) ≫
        SSet.yonedaEquiv.symm
          (ConnectingMap.chosenLift
            (e := S.e) (b := S.b) S.p S.hb σ) := by
              rw [hFace]
    _ = RelativeMorphism.map
        (ConnectingMap.chosenLiftPt
          (e := S.e) (b := S.b) S.p S.hb σ) :=
            (ConnectingMap.chosenLift_face_eq
              (e := S.e) (b := S.b) S.p S.hb σ).symm
    _ = RelativeMorphism.map
        (ConnectingMap.connectingPtSimplexRep
          (p := S.p) (e := S.e) S.hb σ) ≫ S.fiberIncl :=
            (ConnectingMap.connectingPtSimplexRep_ι
              (p := S.p) (e := S.e) S.hb σ).symm

private lemma connectingMulFiberMap_face_zero
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    stdSimplex.δ (mulLocalIndex n 0) ≫
        connectingMulFiberMap S hBase =
      RelativeMorphism.map
        (ConnectingMap.connectingPtSimplexRep
          (p := S.p) (e := S.e) S.hb σ₂) :=
  connectingMulFiberMap_face S hBase 0 σ₂
    (connectingMulFaces_zero S σ₁ σ₂ σ₁₂)

private lemma connectingMulFiberMap_face_one
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    stdSimplex.δ (mulLocalIndex n 1) ≫
        connectingMulFiberMap S hBase =
      RelativeMorphism.map
        (ConnectingMap.connectingPtSimplexRep
          (p := S.p) (e := S.e) S.hb σ₁₂) :=
  connectingMulFiberMap_face S hBase 1 σ₁₂
    (connectingMulFaces_one S σ₁ σ₂ σ₁₂)

private lemma connectingMulFiberMap_face_two
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    stdSimplex.δ (mulLocalIndex n 2) ≫
        connectingMulFiberMap S hBase =
      RelativeMorphism.map
        (ConnectingMap.connectingPtSimplexRep
          (p := S.p) (e := S.e) S.hb σ₁) :=
  connectingMulFiberMap_face S hBase 2 σ₁
    (connectingMulFaces_two S σ₁ σ₂ σ₁₂)

private lemma connectingMulFiberMap_face_of_lt
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc)
    (j : Fin (n + 3)) (hj : j < mulLocalIndex n 0) :
    stdSimplex.δ j ≫ connectingMulFiberMap S hBase =
      SSet.const S.fiberPoint := by
  have hjg : j.castSucc < mulGlobalIndex n 0 := by
    simpa [Fin.lt_def, mulLocalIndex, mulGlobalIndex] using hj
  have hjLast : j.castSucc ≠ Fin.last (n + 3) := by
    exact ne_of_lt (hjg.trans_le (Fin.le_last _))
  apply (cancel_mono S.fiberIncl).mp
  calc
    (stdSimplex.δ j ≫ connectingMulFiberMap S hBase) ≫
        S.fiberIncl =
      stdSimplex.δ j ≫
        (connectingMulFiberMap S hBase ≫ S.fiberIncl) := by
          rw [Category.assoc]
    _ = stdSimplex.δ j ≫ connectingMulFinalFace S hBase := by
      rw [connectingMulFiberMap_ι]
    _ = (stdSimplex.δ j ≫
          stdSimplex.δ (Fin.last (n + 3))) ≫
        connectingMulLift S hBase := by
          rfl
    _ = (stdSimplex.δ (Fin.last (n + 2)) ≫
          stdSimplex.δ j.castSucc) ≫
        connectingMulLift S hBase := by
          rw [show Fin.last (n + 3) =
            (Fin.last (n + 2)).succ by rfl]
          simp only [Category.assoc]
          rw [stdSimplex.δ_comp_δ_assoc (Fin.le_last _)]
    _ = stdSimplex.δ (Fin.last (n + 2)) ≫
        (stdSimplex.δ j.castSucc ≫ connectingMulLift S hBase) := by
          rw [Category.assoc]
    _ = stdSimplex.δ (Fin.last (n + 2)) ≫
        connectingMulFaces S σ₁ σ₂ σ₁₂ j.castSucc hjLast := by
          rw [connectingMulLift_face]
    _ = stdSimplex.δ (Fin.last (n + 2)) ≫ SSet.const S.e := by
      rw [connectingMulFaces_of_lt S σ₁ σ₂ σ₁₂ j.castSucc hjg]
    _ = SSet.const S.e := by rw [SSet.comp_const]
    _ = SSet.const S.fiberPoint ≫ S.fiberIncl := by
      rw [SSet.const_comp]
      rfl

private noncomputable def connectingMulStruct
    (S : FibrationSequence.{u}) [Fibration S.p] {n : ℕ}
    {σ₁ σ₂ σ₁₂ : S.B.PtSimplex (n + 2) S.b}
    (hBase : PtSimplex.MulStruct σ₁ σ₂ σ₁₂
      (Fin.last n).castSucc) :
    PtSimplex.MulStruct
      (ConnectingMap.connectingPtSimplexRep
        (p := S.p) (e := S.e) S.hb σ₁)
      (ConnectingMap.connectingPtSimplexRep
        (p := S.p) (e := S.e) S.hb σ₂)
      (ConnectingMap.connectingPtSimplexRep
        (p := S.p) (e := S.e) S.hb σ₁₂)
      (Fin.last n) where
  map := connectingMulFiberMap S hBase
  δ_castSucc_castSucc_map := by
    rw [← mulLocalIndex_zero_eq,
      connectingMulFiberMap_face_zero]
  δ_succ_castSucc_map := by
    rw [← mulLocalIndex_one_eq,
      connectingMulFiberMap_face_one]
  δ_succ_succ_map := by
    rw [← mulLocalIndex_two_eq,
      connectingMulFiberMap_face_two]
  δ_map_of_lt j hj := by
    apply connectingMulFiberMap_face_of_lt S hBase j
    rw [mulLocalIndex_zero_eq]
    exact hj
  δ_map_of_gt j hj := by
    exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- Let S be a pointed simplicial fibration p:E→B in universe u, with Kan B, p(e)=b and strict fiber
F. For n∈ℕ and a,b′∈π_{n+2}(B,b), δ_{n+1}(a·b′)=δ_{n+1}(a)·δ_{n+1}(b′) in π_{n+1}(F,e). The
target degree is positive. -/
theorem connectingMap_mul
    (S : FibrationSequence.{u}) (n : ℕ)
    (a b : KanComplex.π (n + 2) S.B S.b) :
    S.connectingMap (n + 1) (a * b) =
      S.connectingMap (n + 1) a * S.connectingMap (n + 1) b := by
  let _ : Fibration S.p := S.fibration_p
  induction a using KanComplex.π.rec with
  | mk σ₁ =>
    induction b using KanComplex.π.rec with
    | mk σ₂ =>
      obtain ⟨σ₁₂, ⟨hBase⟩⟩ :=
        PtSimplex.MulStruct.nonempty σ₁ σ₂ (Fin.last n).castSucc
      rw [hBase.mul_eq_penultimate]
      rw [S.connectingMap_mk, S.connectingMap_mk,
        S.connectingMap_mk]
      exact (connectingMulStruct S hBase).mul_eq.symm

/-- Let S be a pointed simplicial fibration p:E→B in universe u, with Kan B, p(e)=b and strict fiber
F. If g₁,g₂∈π₁(B,b) satisfy δ₀(g₁)=δ₀(g₂) in π₀(F,e), there is v∈π₁(E,e) such that g₂=g₁·p_*(v).
The correction factor is on the right. -/
theorem eq_mul_of_connectingMap_zero_eq
    (S : FibrationSequence.{u})
    (g₁ g₂ : KanComplex.π 1 S.B S.b)
    (h : S.connectingMap 0 g₁ = S.connectingMap 0 g₂) :
    ∃ v : KanComplex.π 1 S.E S.e,
      g₂ = g₁ * KanComplex.π.map S.p S.hb 1 v := by
  let _ : Fibration S.p := S.fibration_p
  induction g₁ using KanComplex.π.rec with
  | mk s₁ =>
    induction g₂ using KanComplex.π.rec with
    | mk s₂ =>
      rw [S.connectingMap_mk, S.connectingMap_mk,
        KanComplex.π.mk_eq_mk_iff] at h
      obtain ⟨hrel⟩ := h
      let r₁ := ConnectingMap.connectingPtSimplexRep
        (p := S.p) (e := S.e) S.hb s₁
      let r₂ := ConnectingMap.connectingPtSimplexRep
        (p := S.p) (e := S.e) S.hb s₂
      let k : Edge (PtSimplex.equiv₀ S.fiberPoint r₂)
          (PtSimplex.equiv₀ S.fiberPoint r₁) :=
        PtSimplex.RelStruct₀.equiv₀ hrel
      let kInvFiber := k.inv
      let kInvTotal₀ := kInvFiber.map S.fiberIncl
      let kInvTotal : Edge
          (PtSimplex.equiv₀ S.e
            (ConnectingMap.chosenLiftPt
              (e := S.e) (b := S.b) S.p S.hb s₁))
          (PtSimplex.equiv₀ S.e
            (ConnectingMap.chosenLiftPt
              (e := S.e) (b := S.b) S.p S.hb s₂)) :=
        kInvTotal₀.ofEq
          (connectingVertex_fiberIncl S s₁)
          (connectingVertex_fiberIncl S s₂)
      let l₁ := chosenLiftEdge S s₁
      let l₂ := chosenLiftEdge S s₂
      let middle := l₁.inv.comp kInvTotal
      let middleStruct := l₁.inv.compStruct kInvTotal
      let loop := middle.comp l₂
      let loopStruct := middle.compStruct l₂
      let loopPt := ptSimplexOneOfLoopEdge loop
      let hs₁ := chosenLiftVertex_p S s₁
      let hs₂ := chosenLiftVertex_p S s₂
      let l₁p : Edge S.b S.b := (l₁.map S.p).ofEq hs₁ S.hb
      let l₁Invp : Edge S.b S.b := (l₁.inv.map S.p).ofEq S.hb hs₁
      let kp : Edge S.b S.b := (kInvTotal.map S.p).ofEq hs₁ hs₂
      let middlep : Edge S.b S.b := (middle.map S.p).ofEq S.hb hs₂
      let loopp : Edge S.b S.b := (loop.map S.p).ofEq S.hb S.hb
      let l₂p : Edge S.b S.b := (l₂.map S.p).ofEq hs₂ S.hb
      let idp : Edge S.b S.b :=
        ((Edge.id
          (PtSimplex.equiv₀ S.e
            (ConnectingMap.chosenLiftPt
              (e := S.e) (b := S.b) S.p S.hb s₁))).map S.p).ofEq hs₁ hs₁
      let inverseStructp : Edge.CompStruct l₁p l₁Invp idp :=
        (l₁.homInvId.map S.p).ofEq rfl rfl rfl
      let middleStructp : Edge.CompStruct l₁Invp kp middlep :=
        (middleStruct.map S.p).ofEq rfl rfl rfl
      let loopStructp : Edge.CompStruct middlep l₂p loopp :=
        (loopStruct.map S.p).ofEq rfl rfl rfl
      have hl₁p : l₁p = edgeOfPtSimplexOne s₁ := by
        exact chosenLiftEdge_map_p S s₁ hs₁
      have hl₂p : l₂p = edgeOfPtSimplexOne s₂ := by
        exact chosenLiftEdge_map_p S s₂ hs₂
      have hidp : idp = Edge.id S.b := by
        apply Edge.ext
        change (((Edge.id
            (PtSimplex.equiv₀ S.e
              (ConnectingMap.chosenLiftPt
                (e := S.e) (b := S.b) S.p S.hb s₁))).map S.p).ofEq
                  hs₁ hs₁).edge = (Edge.id S.b).edge
        change ((Edge.id
            (PtSimplex.equiv₀ S.e
              (ConnectingMap.chosenLiftPt
                (e := S.e) (b := S.b) S.p S.hb s₁))).map S.p).edge =
          (Edge.id S.b).edge
        rw [Edge.map_id]
        change S.B.σ 0
            (S.p.app _
              (PtSimplex.equiv₀ S.e
                (ConnectingMap.chosenLiftPt
                  (e := S.e) (b := S.b) S.p S.hb s₁))) =
          S.B.σ 0 S.b
        exact congrArg (S.B.σ 0) hs₁
      have hkp : kp = Edge.id S.b := by
        apply Edge.ext
        change S.p.app _ (S.fiberIncl.app _ kInvFiber.edge) =
          S.B.σ 0 S.b
        have hcomp :
            (S.fiberIncl ≫ S.p).app (Opposite.op ⦋1⦌) kInvFiber.edge =
              (SSet.const S.b).app (Opposite.op ⦋1⦌) kInvFiber.edge := by
          exact ConcreteCategory.congr_hom
            (congr_app S.fiberIncl_comp (Opposite.op ⦋1⦌)) kInvFiber.edge
        calc
          S.p.app _ (S.fiberIncl.app _ kInvFiber.edge) =
              (S.fiberIncl ≫ S.p).app (Opposite.op ⦋1⦌)
                kInvFiber.edge := rfl
          _ = (SSet.const S.b).app (Opposite.op ⦋1⦌)
                kInvFiber.edge := hcomp
          _ = S.B.σ 0 S.b := by
            change SSet.yonedaEquiv
                (SSet.const (X := Δ[1]) S.b) = S.B.σ 0 S.b
            exact (SSet.σ_zero_eq_yonedaEquiv_const S.b).symm
      have hcomp :
          FundamentalGroupoid.homMk l₁p ≫
              FundamentalGroupoid.homMk loopp =
            FundamentalGroupoid.homMk l₂p := by
        calc
          FundamentalGroupoid.homMk l₁p ≫
                FundamentalGroupoid.homMk loopp =
              FundamentalGroupoid.homMk l₁p ≫
                (FundamentalGroupoid.homMk middlep ≫
                  FundamentalGroupoid.homMk l₂p) := by
                    rw [loopStructp.homMk_comp]
          _ = (FundamentalGroupoid.homMk l₁p ≫
                FundamentalGroupoid.homMk middlep) ≫
                  FundamentalGroupoid.homMk l₂p := by
                    rw [Category.assoc]
          _ = (FundamentalGroupoid.homMk l₁p ≫
                (FundamentalGroupoid.homMk l₁Invp ≫
                  FundamentalGroupoid.homMk kp)) ≫
                  FundamentalGroupoid.homMk l₂p := by
                    rw [middleStructp.homMk_comp]
          _ = ((FundamentalGroupoid.homMk l₁p ≫
                FundamentalGroupoid.homMk l₁Invp) ≫
                  FundamentalGroupoid.homMk kp) ≫
                  FundamentalGroupoid.homMk l₂p := by
                    simp only [Category.assoc]
          _ = ((FundamentalGroupoid.homMk idp) ≫
                  FundamentalGroupoid.homMk kp) ≫
                  FundamentalGroupoid.homMk l₂p := by
                    rw [inverseStructp.homMk_comp]
          _ = FundamentalGroupoid.homMk l₂p := by
                    rw [hidp, hkp, FundamentalGroupoid.homMk_id]
                    simp
      obtain ⟨baseStruct⟩ :=
        (FundamentalGroupoid.homMk_comp_iff.mp hcomp)
      let baseStruct' : Edge.CompStruct
          (edgeOfPtSimplexOne s₁) loopp (edgeOfPtSimplexOne s₂) :=
        baseStruct.ofEq
          (congrArg Edge.edge hl₁p)
          rfl
          (congrArg Edge.edge hl₂p)
      have hloopPt : SSet.PtSimplex.map S.p S.hb loopPt =
          ptSimplexOneOfLoopEdge loopp := by
        apply RelativeMorphism.ext
        change SSet.yonedaEquiv.symm loop.edge ≫ S.p =
          SSet.yonedaEquiv.symm loopp.edge
        have hloopp : loopp.edge = (loop.map S.p).edge := rfl
        rw [hloopp, Edge.map_edge]
        exact SSet.yonedaEquiv_symm_comp loop.edge S.p
      refine ⟨KanComplex.π.mk loopPt, ?_⟩
      rw [KanComplex.π.map_mk, hloopPt]
      simpa only [ptSimplexOneOfLoopEdge_edgeOfPtSimplexOne] using
        (mul_mk_eq_of_compStruct baseStruct').symm

private theorem injective_zero_of_subsingleton_total
    (S : FibrationSequence.{u})
    (hE : ∀ n, Subsingleton (KanComplex.π n S.E S.e)) :
    Function.Injective (S.connectingMap 0) := by
  intro g₁ g₂ h
  obtain ⟨v, hv⟩ := S.eq_mul_of_connectingMap_zero_eq g₁ g₂ h
  have hvOne : v = 1 := Subsingleton.elim _ _
  rw [hvOne, KanComplex.π.map_one] at hv
  have hBaseConst :
      KanComplex.π.mk (RelativeMorphism.const : S.B.PtSimplex 1 S.b) =
        g₁⁻¹ * g₁ :=
    mk_const_eq_inv_mul S.b 0 g₁
  calc
    g₁ = g₁ * (g₁⁻¹ * g₁) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = g₁ * KanComplex.π.mk
        (RelativeMorphism.const : S.B.PtSimplex 1 S.b) := by rw [hBaseConst]
    _ = g₂ := hv.symm

private theorem injective_positive_of_mul_of_subsingleton_total
    (S : FibrationSequence.{u})
    (hMul : ∀ (n : ℕ) (a b : KanComplex.π (n + 2) S.B S.b),
      S.connectingMap (n + 1) (a * b) =
        S.connectingMap (n + 1) a * S.connectingMap (n + 1) b)
    (hE : ∀ n, Subsingleton (KanComplex.π n S.E S.e))
    (n : ℕ) : Function.Injective (S.connectingMap (n + 1)) := by
  intro a b hab
  have hBaseConst :
      KanComplex.π.mk
          (RelativeMorphism.const : S.B.PtSimplex (n + 2) S.b) =
        b⁻¹ * b :=
    mk_const_eq_inv_mul S.b (n + 1) b
  have hConnectingConst :
      S.connectingMap (n + 1)
          (KanComplex.π.mk
            (RelativeMorphism.const : S.B.PtSimplex (n + 2) S.b)) =
        KanComplex.π.mk
          (RelativeMorphism.const : S.fiber.PtSimplex (n + 1)
            S.fiberPoint) := by
    have hMapOne := S.connectingMap_map_eq_one
      (n := n + 1) (1 : KanComplex.π (n + 2) S.E S.e)
    change S.connectingMap (n + 1)
        (KanComplex.π.map S.p S.hb (n + 2)
          (KanComplex.π.mk
            (RelativeMorphism.const : S.E.PtSimplex (n + 2) S.e))) =
      KanComplex.π.mk
        (RelativeMorphism.const :
          S.fiber.PtSimplex (n + 1) S.fiberPoint) at hMapOne
    rw [KanComplex.π.map_mk] at hMapOne
    have hmap : SSet.PtSimplex.map S.p S.hb
        (RelativeMorphism.const : S.E.PtSimplex (n + 2) S.e) =
          (RelativeMorphism.const : S.B.PtSimplex (n + 2) S.b) := by
      apply RelativeMorphism.ext
      change SSet.const (X := Δ[n + 2]) S.e ≫ S.p =
        SSet.const (X := Δ[n + 2]) S.b
      rw [SSet.const_comp, S.hb]
    rw [hmap] at hMapOne
    exact hMapOne
  have hTargetConst :
      KanComplex.π.mk
          (RelativeMorphism.const : S.fiber.PtSimplex (n + 1)
            S.fiberPoint) =
        (S.connectingMap (n + 1) b)⁻¹ * S.connectingMap (n + 1) b :=
    mk_const_eq_inv_mul S.fiberPoint n (S.connectingMap (n + 1) b)
  have hOne : S.connectingMap (n + 1) (b⁻¹ * a) = 1 := by
    rw [hMul, hab]
    have hInv : S.connectingMap (n + 1) b⁻¹ =
        (S.connectingMap (n + 1) b)⁻¹ := by
      apply mul_right_cancel (b := S.connectingMap (n + 1) b)
      calc
        S.connectingMap (n + 1) b⁻¹ * S.connectingMap (n + 1) b =
            S.connectingMap (n + 1) (b⁻¹ * b) :=
              (hMul n b⁻¹ b).symm
        _ = S.connectingMap (n + 1)
            (KanComplex.π.mk
              (RelativeMorphism.const :
                S.B.PtSimplex (n + 2) S.b)) := by
                  rw [hBaseConst]
        _ = KanComplex.π.mk
            (RelativeMorphism.const :
              S.fiber.PtSimplex (n + 1) S.fiberPoint) := hConnectingConst
        _ = (S.connectingMap (n + 1) b)⁻¹ *
            S.connectingMap (n + 1) b := hTargetConst
    rw [hInv]
    exact hTargetConst.symm
  obtain ⟨v, hv⟩ := S.exactness_at_B (b⁻¹ * a) hOne
  have hvOne : v = 1 := Subsingleton.elim _ _
  rw [hvOne, KanComplex.π.map_one] at hv
  have hq : b⁻¹ * a =
      KanComplex.π.mk
        (RelativeMorphism.const : S.B.PtSimplex (n + 2) S.b) := hv.symm
  exact mul_left_cancel (hq.trans hBaseConst)

private theorem surjective_of_subsingleton_total
    (S : FibrationSequence.{u})
    (hE : ∀ n, Subsingleton (KanComplex.π n S.E S.e))
    (n : ℕ) : Function.Surjective (S.connectingMap n) := by
  intro q
  apply S.exactness_at_fiber q
  exact Subsingleton.elim _ _

/-- Let S be a pointed simplicial fibration p:E→B in universe u, with Kan B, p(e)=b and strict fiber
F. If π_k(E,e) is subsingleton for every k∈ℕ, then δ_n:π_{n+1}(B,b)→π_n(F,e) is bijective for
every n∈ℕ, including n=0. -/
theorem connectingMap_bijective_of_subsingleton_total
    (S : FibrationSequence.{u})
    (hE : ∀ n, Subsingleton (KanComplex.π n S.E S.e))
    (n : ℕ) :
    Function.Bijective (S.connectingMap n) := by
  constructor
  · obtain _ | n := n
    · exact injective_zero_of_subsingleton_total S hE
    · exact injective_positive_of_mul_of_subsingleton_total
        S (connectingMap_mul S) hE n
  · exact surjective_of_subsingleton_total S hE n

end SSet.FibrationSequence
