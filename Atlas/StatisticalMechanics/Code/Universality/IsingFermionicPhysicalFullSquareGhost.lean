/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFiniteGhostComparison
import Code.Universality.IsingFermionicPhysicalRangeTransfer
import Code.Universality.IsingFermionicSquareWiredFullFaces
















open SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

abbrev FKIsingSquareFullVertexNode (n : Nat) :=
  (fkSquareBoxPlanar n).V

abbrev FKIsingSquareFullFaceNode (n : Nat) :=
  FKIsingSquareInteriorCell n


def fkIsingSquareFullFaceOfKey
    (n : Nat) (p : Int × Int) (hp : fkIsingSquareInteriorFaceKey n p) :
    FKIsingSquareFullFaceNode n := by
  refine (⟨(p.1 + n).toNat, ?_⟩, ⟨(p.2 + n).toNat, ?_⟩)
  · rcases hp with ⟨hp0, hp1, -, -⟩
    omega
  · rcases hp with ⟨-, -, hp0, hp1⟩
    omega

@[simp] theorem fkIsingSquareFullFaceOfKey_key
    (n : Nat) (p : Int × Int) (hp : fkIsingSquareInteriorFaceKey n p) :
    fkIsingSquareInteriorCellKey n (fkIsingSquareFullFaceOfKey n p hp) = p := by
  rcases hp with ⟨hp0, hp1, hp2, hp3⟩
  apply Prod.ext <;>
    simp [fkIsingSquareInteriorCellKey, fkIsingSquareFullFaceOfKey,
      Int.toNat_of_nonneg] <;> omega


noncomputable def fkIsingSquareFullFaceOfRadialIncidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    FKIsingSquareFullFaceNode n :=
  fkIsingSquareFullFaceOfKey n
    (fkIsingSquareInteriorRadialFaceKey n hn e)
    (fkIsingSquareInteriorRadialFaceKey_isInterior n hn e)

@[simp] theorem fkIsingSquareFullFaceOfRadialIncidence_key
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareInteriorCellKey n
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      fkIsingSquareInteriorRadialFaceKey n hn e := by
  exact fkIsingSquareFullFaceOfKey_key n _ _


def fkIsingSquareFullVertexGraph (n : Nat) :
    SimpleGraph (FKIsingSquareFullVertexNode n) :=
  (fkSquareBoxPlanar n).G


def fkIsingSquareFullFaceGraph (n : Nat) :
    SimpleGraph (FKIsingSquareFullFaceNode n) where
  Adj p q :=
    (p.1 = q.1 ∧ (p.2.1 + 1 = q.2.1 ∨ q.2.1 + 1 = p.2.1)) ∨
      (p.2 = q.2 ∧ (p.1.1 + 1 = q.1.1 ∨ q.1.1 + 1 = p.1.1))
  symm := by
    rintro p q (h | h)
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro p h
    rcases h with h | h <;> rcases h.2 with h | h <;> omega


def fkIsingSquareFullVertexFixedBoundary
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Prop :=
  fkIsingSquareWiredArc n x



def fkIsingSquareFullVertexGhostMultiplicity
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (if x.1 1 = -(n : Int) then 1 else 0) +
    (if x.1 0 = (n : Int) then 1 else 0) +
      (if x.1 1 = (n : Int) then 1 else 0)



def fkIsingSquareFullFaceFixedBoundary
    (n : Nat) (c : FKIsingSquareFullFaceNode n) : Prop :=
  c.2.1 = 0 ∨ c.1.1 + 1 = 2 * n ∨ c.2.1 + 1 = 2 * n


def fkIsingSquareFullFaceGhostMultiplicity
    (_n : Nat) (c : FKIsingSquareFullFaceNode _n) : Nat :=
  if c.1.1 = 0 then 1 else 0

theorem fkIsingSquareFullVertexGhostMultiplicity_pos_iff
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    0 < fkIsingSquareFullVertexGhostMultiplicity n x ↔
      x.1 1 = -(n : Int) ∨ x.1 0 = (n : Int) ∨
        x.1 1 = (n : Int) := by
  unfold fkIsingSquareFullVertexGhostMultiplicity
  by_cases hs : x.1 1 = -(n : Int) <;>
    by_cases he : x.1 0 = (n : Int) <;>
    by_cases hnorth : x.1 1 = (n : Int) <;>
    simp [hs, he, hnorth]

theorem fkIsingSquareFullFaceGhostMultiplicity_pos_iff
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    0 < fkIsingSquareFullFaceGhostMultiplicity n c ↔ c.1.1 = 0 := by
  unfold fkIsingSquareFullFaceGhostMultiplicity
  by_cases h : c.1.1 = 0 <;> simp [h]



theorem fkIsingSquareFullVertex_boundary_fixed_or_ghost
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareBoxBoundary n x) :
    fkIsingSquareFullVertexFixedBoundary n x ∨
      0 < fkIsingSquareFullVertexGhostMultiplicity n x := by
  rcases hx with ⟨i, hi⟩
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff]
  fin_cases i
  · rcases Int.natAbs_eq_iff.mp hi with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
  · rcases Int.natAbs_eq_iff.mp hi with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)


theorem fkIsingSquareFullVertex_reaches_fixed_or_ghost
    (n : Nat) :
    ∀ x : FKIsingSquareFullVertexNode n, ∃ b,
      (fkIsingSquareFullVertexFixedBoundary n b ∨
          0 < fkIsingSquareFullVertexGhostMultiplicity n b) ∧
        (fkIsingSquareFullVertexGraph n).Reachable x b := by
  intro x
  refine ⟨fkIsingSquareMarkedA n, Or.inl ?_, ?_⟩
  · exact fkIsingSquareMarkedA_mem_wiredArc n
  · exact StatMech.FrontierB.boxGraph_preconnected 2 n x
      (fkIsingSquareMarkedA n)


theorem fkIsingSquareFullFace_reaches_fixed_or_ghost
    (n : Nat) :
    ∀ c : FKIsingSquareFullFaceNode n, ∃ b,
      (fkIsingSquareFullFaceFixedBoundary n b ∨
          0 < fkIsingSquareFullFaceGhostMultiplicity n b) ∧
        (fkIsingSquareFullFaceGraph n).Reachable c b := by
  let P : Nat → Prop := fun k ↦
    ∀ c : FKIsingSquareFullFaceNode n, c.2.1 = k → ∃ b,
      (fkIsingSquareFullFaceFixedBoundary n b ∨
          0 < fkIsingSquareFullFaceGhostMultiplicity n b) ∧
        (fkIsingSquareFullFaceGraph n).Reachable c b
  suffices ∀ k, P k by
    intro c
    exact this c.2.1 c rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro c hck
      by_cases hk : k = 0
      · have hc0 : c.2.1 = 0 := hck.trans hk
        refine ⟨c, Or.inl ?_, SimpleGraph.Reachable.refl c⟩
        exact Or.inl hc0
      · let q : FKIsingSquareFullFaceNode n :=
          (c.1, ⟨c.2.1 - 1, by omega⟩)
        have hqk : q.2.1 < k := by simp [q]; omega
        obtain ⟨b, hb, hqb⟩ := ih q.2.1 hqk q rfl
        refine ⟨b, hb, ?_⟩
        have hcq : (fkIsingSquareFullFaceGraph n).Adj c q := by
          apply Or.inl
          exact ⟨rfl, Or.inr (by simp [q]; omega)⟩
        exact hcq.reachable.trans hqb



theorem fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic
    (n : Nat) (H : FKIsingSquareFullVertexNode n → Real)
    (hmodified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) H x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - H x) ≤ 0)
    (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ H x) :
    ∀ x, 0 ≤ H x := by
  exact isingFermionicGhost_const_le_superharmonic_boundaryWith
    (fkIsingSquareFullVertexGraph n)
    (fkIsingSquareFullVertexGhostMultiplicity n)
    (fkIsingSquareFullVertexFixedBoundary n) H 1 0
    (fkIsingSquareFullVertex_reaches_fixed_or_ghost n)
    hmodified (by norm_num) hfixed


theorem fkIsingSquareFullFace_le_one_of_modifiedSubharmonic
    (n : Nat) (H : FKIsingSquareFullFaceNode n → Real)
    (hmodified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - H c))
    (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → H c ≤ 1) :
    ∀ c, H c ≤ 1 := by
  exact isingFermionicGhost_subharmonic_le_const_boundaryWith
    (fkIsingSquareFullFaceGraph n)
    (fkIsingSquareFullFaceGhostMultiplicity n)
    (fkIsingSquareFullFaceFixedBoundary n) H 0 1
    (fkIsingSquareFullFace_reaches_fixed_or_ghost n)
    hmodified (by norm_num) hfixed



def fkIsingSquareRadialPatchPrimalFullVertex
    (n m : Nat) (hm : m ≤ n) :
    FKIsingSquareRadialPatchPrimalNode m → FKIsingSquareFullVertexNode n :=
  fkIsingSquareRadialPatchPrimalNodeVertex n m hm




def fkIsingSquareRadialPatchDualFullFace
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    FKIsingSquareFullFaceNode n := by
  let half := (q.1.1.1 + q.1.2.1 + 1) / 2
  have hmod := Nat.not_even_iff.mp q.2
  have hn : 0 < n := by omega
  refine (⟨n + half - 1, by
      have hi := q.1.1.2
      have hj := q.1.2.2
      omega⟩,
    ⟨n + q.1.1.1 - half, by
      have hi := q.1.1.2
      have hj := q.1.2.2
      omega⟩)

theorem fkIsingSquareRadialPatchDualFullFace_key
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    fkIsingSquareInteriorCellKey n
        (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) =
      (((q.1.1.1 + q.1.2.1 + 1) / 2 : Int) - 1,
        (q.1.1.1 : Int) -
          ((q.1.1.1 + q.1.2.1 + 1) / 2 : Int)) := by
  have hmod := Nat.not_even_iff.mp q.2
  have hi := q.1.1.2
  have hj := q.1.2.2
  apply Prod.ext
  · simp [fkIsingSquareInteriorCellKey,
      fkIsingSquareRadialPatchDualFullFace]
    omega
  · simp [fkIsingSquareInteriorCellKey,
      fkIsingSquareRadialPatchDualFullFace]
    omega

theorem fkIsingSquareRadialPatchDualFullFace_injective
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    Function.Injective
      (fkIsingSquareRadialPatchDualFullFace n m hm hm2) := by
  intro p q hpq
  have h0 := congrArg
    (fun c : FKIsingSquareFullFaceNode n ↦ c.1.1) hpq
  have h1 := congrArg
    (fun c : FKIsingSquareFullFaceNode n ↦ c.2.1) hpq
  simp only [fkIsingSquareRadialPatchDualFullFace] at h0 h1
  have hpmod := Nat.not_even_iff.mp p.2
  have hqmod := Nat.not_even_iff.mp q.2
  have hhalf :
      (p.1.1.1 + p.1.2.1 + 1) / 2 =
        (q.1.1.1 + q.1.2.1 + 1) / 2 := by
    omega
  have hi : p.1.1.1 = q.1.1.1 := by omega
  have hj : p.1.2.1 = q.1.2.1 := by omega
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hi
  · exact Fin.ext hj



theorem fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexH x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) faceH c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - faceH c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
    (hprimalRestriction : ∀ p,
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p =
        vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p))
    (hdualRestriction : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q =
        faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q)) :
    (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ∧
      fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ≤ 1) ∧
      (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ∧
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ≤ 1) := by
  apply fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper
    n m hn hm hm2 base
  · intro p
    rw [hprimalRestriction p]
    exact fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic
      n vertexH hvertexModified hvertexFixed _
  · intro q
    rw [hdualRestriction q]
    exact fkIsingSquareFullFace_le_one_of_modifiedSubharmonic
      n faceH hfaceModified hfaceFixed _

end

end StatMech.Universality
