/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.Crossover
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.FaceComposition

/-!
# Bisimplicial Alexander--Whitney ordinary faces

Faces away from the crossover cut are identified with factored diagonal
faces.  Horizontal faces use back-face naturality, front-face composition,
inner naturality, and interchange.  Vertical faces use back-face composition,
front naturality, and outer face composition.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitney

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- An ordinary horizontal face of a source cut is the corresponding
factored diagonal face followed by the target cut. -/
theorem horizontal_ordinary_face_eq
    (p q n : ℕ) (h : p + q = n) (j : Fin (p + 1)) :
    faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega) ≫
        (B.δ (Fin.castSucc j)).app (Opposite.op ⦋q⦌) =
      ((B.obj (Opposite.op ⦋n + 1⦌)).δ
          (⟨j.val, by omega⟩ : Fin (n + 2)) ≫
        (B.δ (⟨j.val, by omega⟩ : Fin (n + 2))).app
          (Opposite.op ⦋n⦌)) ≫
        faceToBidegreeOfEq B p q n h := by
  subst n
  unfold faceToBidegreeOfEq
  let outer := B.δ (Fin.castSucc j)
  let global : Fin (p + q + 2) := ⟨j.val, by omega⟩
  let fS := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show (p + 1) + q = p + q + 1 by omega)).app
        (Opposite.op ⦋p + q + 1⦌)
  let bS := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p + 1⦌))
      (show (p + 1) + q = p + q + 1 by omega)
  let fT := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + q = p + q by rfl)).app (Opposite.op ⦋p + q⦌)
  let bT := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p⦌)) (show p + q = p + q by rfl)
  let fTN := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + q = p + q by rfl)).app (Opposite.op ⦋p + q + 1⦌)
  let bM := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p⦌))
      (show (p + 1) + q = p + q + 1 by omega)
  let dN := (B.obj (Opposite.op ⦋p + q + 1⦌)).δ global
  let dn := (B.obj (Opposite.op ⦋p + q⦌)).δ global
  let oN := (B.δ global).app (Opposite.op ⦋p + q + 1⦌)
  let on := (B.δ global).app (Opposite.op ⦋p + q⦌)
  let dP := (B.obj (Opposite.op ⦋p⦌)).δ global
  let oq := outer.app (Opposite.op ⦋q⦌)
  let oN' := outer.app (Opposite.op ⦋p + q + 1⦌)
  have hbNat := AlgebraicTopology.AlexanderWhitney.backFace_naturality
    outer (show (p + 1) + q = p + q + 1 by omega)
  have hfComp := AlgebraicTopology.AlexanderWhitney.frontFace_comp_delta
    (C := SimplicialObject A) B p q (Fin.castSucc j)
  have hfCompApp := congrArg (fun k => k.app (Opposite.op ⦋p + q + 1⦌)) hfComp
  have hfNat := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + q = p + q by rfl)).naturality
      (SimplexCategory.δ global).op
  have houterNat := (B.δ global).naturality (SimplexCategory.δ global).op
  have hbComp :
      (B.obj (Opposite.op ⦋p⦌)).δ (⟨j.val, by omega⟩ : Fin (p + q + 2)) ≫
          AlgebraicTopology.AlexanderWhitney.backFace (B.obj (Opposite.op ⦋p⦌))
            (show p + q = p + q by rfl) =
        AlgebraicTopology.AlexanderWhitney.backFace (B.obj (Opposite.op ⦋p⦌))
          (show (p + 1) + q = p + q + 1 by omega) :=
    (B.obj (Opposite.op ⦋p⦌)).δ_δ₀Iter p ⟨j.val, by omega⟩
  change bS ≫ oq = oN' ≫ bM at hbNat
  change fS ≫ oN' = oN ≫ fTN at hfCompApp
  change dn ≫ fT = fTN ≫ dP at hfNat
  change dN ≫ on = oN ≫ dn at houterNat
  change dP ≫ bT = bM at hbComp
  change (fS ≫ bS) ≫ outer.app (Opposite.op ⦋q⦌) =
    (dN ≫ on) ≫ (fT ≫ bT)
  calc
    _ = fS ≫ oN' ≫ bM := by
      simpa only [Category.assoc] using fS ≫= hbNat
    _ = oN ≫ fTN ≫ bM := by
      simpa only [Category.assoc] using hfCompApp =≫ bM
    _ = oN ≫ fTN ≫ dP ≫ bT := by
      simpa only [Category.assoc] using
        oN ≫= ((fTN ≫= hbComp).symm)
    _ = oN ≫ dn ≫ fT ≫ bT := by
      simpa only [Category.assoc] using
        oN ≫= (hfNat.symm =≫ bT)
    _ = dN ≫ on ≫ fT ≫ bT := by
      simpa only [Category.assoc] using
        houterNat.symm =≫ (fT ≫ bT)
    _ = _ := by simp only [Category.assoc]

/-- An ordinary vertical face of a source cut is the corresponding factored
diagonal face followed by the target cut. -/
theorem vertical_ordinary_face_eq
    (p q n : ℕ) (h : p + q = n) (k : Fin (q + 1)) :
    faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega) ≫
        (B.obj (Opposite.op ⦋p⦌)).δ (Fin.succ k) =
      ((B.obj (Opposite.op ⦋n + 1⦌)).δ
          (⟨p + 1 + k.val, by omega⟩ : Fin (n + 2)) ≫
        (B.δ (⟨p + 1 + k.val, by omega⟩ : Fin (n + 2))).app
          (Opposite.op ⦋n⦌)) ≫
        faceToBidegreeOfEq B p q n h := by
  subst n
  unfold faceToBidegreeOfEq
  let global : Fin (p + q + 2) := ⟨p + 1 + k.val, by omega⟩
  let globalComp : Fin (p + q + 2) :=
    ⟨p + (Fin.succ k).val, by omega⟩
  let fS := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + (q + 1) = p + q + 1 by omega)).app
        (Opposite.op ⦋p + q + 1⦌)
  let bS := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p⦌))
      (show p + (q + 1) = p + q + 1 by omega)
  let fSn := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + (q + 1) = p + q + 1 by omega)).app
        (Opposite.op ⦋p + q⦌)
  let fT := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + q = p + q by rfl)).app (Opposite.op ⦋p + q⦌)
  let bT := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p⦌)) (show p + q = p + q by rfl)
  let dN := (B.obj (Opposite.op ⦋p + q + 1⦌)).δ global
  let dP := (B.obj (Opposite.op ⦋p⦌)).δ global
  let dPComp := (B.obj (Opposite.op ⦋p⦌)).δ globalComp
  let on := (B.δ global).app (Opposite.op ⦋p + q⦌)
  let inner := (B.obj (Opposite.op ⦋p⦌)).δ (Fin.succ k)
  have hbComp :
      AlgebraicTopology.AlexanderWhitney.backFace (B.obj (Opposite.op ⦋p⦌))
            (show p + (q + 1) = p + q + 1 by omega) ≫
          (B.obj (Opposite.op ⦋p⦌)).δ (Fin.succ k) =
        (B.obj (Opposite.op ⦋p⦌)).δ (⟨p + (Fin.succ k).val, by omega⟩ : Fin (p + q + 2)) ≫
          AlgebraicTopology.AlexanderWhitney.backFace (B.obj (Opposite.op ⦋p⦌))
            (show p + q = p + q by rfl) :=
    ((B.obj (Opposite.op ⦋p⦌)).δ_δ₀Iter' (n := q) (m := p + q) (Fin.succ k) p
      ⟨p + (Fin.succ k).val, by omega⟩ (by omega) (Nat.add_comm _ _)).symm
  have hfNat := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + (q + 1) = p + q + 1 by omega)).naturality
        (SimplexCategory.δ global).op
  have hfComp := AlgebraicTopology.AlexanderWhitney.delta_comp_frontFace
    (C := SimplicialObject A) B p q k
  have hfCompApp := congrArg (fun t => t.app (Opposite.op ⦋p + q⦌)) hfComp
  change bS ≫ inner = dPComp ≫ bT at hbComp
  have hglobal : globalComp = global := by
    ext
    simp [globalComp, global]
    omega
  have hdP : dPComp = dP := congrArg
    (fun t => (B.obj (Opposite.op ⦋p⦌)).δ t) hglobal
  have hbComp' : dP ≫ bT = bS ≫ inner := by
    rw [← hdP]
    exact hbComp.symm
  change dN ≫ fSn = fS ≫ dP at hfNat
  change on ≫ fT = fSn at hfCompApp
  change (fS ≫ bS) ≫ inner = (dN ≫ on) ≫ (fT ≫ bT)
  calc
    _ = fS ≫ dP ≫ bT := by
      simpa only [Category.assoc] using fS ≫= hbComp'.symm
    _ = dN ≫ fSn ≫ bT := by
      simpa only [Category.assoc] using hfNat.symm =≫ bT
    _ = dN ≫ on ≫ fT ≫ bT := by
      simpa only [Category.assoc] using dN ≫= (hfCompApp.symm =≫ bT)
    _ = _ := by simp only [Category.assoc]

end AlgebraicTopology.BisimplicialAlexanderWhitney
