/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# Tests for special outer horn filling in all dimensions (packet T21)

Statement checks for
`MathlibExt/AlgebraicTopology/Quasicategory/SpecialOuterHornGeneral.lean`:
Joyal's special outer horn filling in every dimension, on the left
(`SSet.exists_fill_horn_left_of_isEquivalence`) and on the right
(`SSet.exists_fill_horn_right_of_isEquivalence`), generalizing the
cases `n = 0` (`CoreKan.lean`) and `n = 1`
(`SpecialOuterHorn.lean`, packet T18), its abstract core
`SSet.exists_filler_simplex_of_leftData`, and the assembled
consequences `SSet.hasSpecialOuterHornFilling_of_quasicategory`
and `SSet.kanComplex_core_of_quasicategory`. The examples below
pin the statements (not the proofs), including concrete instances
in dimensions `2` to `5` on both sides.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X : SSet.{u}} {Y : SSet.{u}} [Quasicategory X]

section LeftDimensionChecks

/-- `n = 0`: filling of `Λ[2, 0]` with the `(0, 1)`-edge an
equivalence, compare `exists_fill_horn_two_zero_of_isEquivalence`
in `CoreKan.lean`. -/
example (σ₀ : (Λ[0 + 2, (0 : Fin (0 + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[0 + 2] ⟶ X, σ₀ = Λ[0 + 2, (0 : Fin (0 + 3))].ι ≫ σ :=
  exists_fill_horn_left_of_isEquivalence σ₀ h

/-- `n = 1`: filling of `Λ[3, 0]` with the `(0, 1)`-edge an
equivalence, compare `exists_fill_horn_three_zero_of_isEquivalence`
(packet T18). -/
example (σ₀ : (Λ[1 + 2, (0 : Fin (1 + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[1 + 2] ⟶ X, σ₀ = Λ[1 + 2, (0 : Fin (1 + 3))].ι ≫ σ :=
  exists_fill_horn_left_of_isEquivalence σ₀ h

/-- `n = 2`: filling of `Λ[4, 0]` with the `(0, 1)`-edge an
equivalence; the first dimension not covered by packet T18. -/
example (σ₀ : (Λ[2 + 2, (0 : Fin (2 + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[2 + 2] ⟶ X, σ₀ = Λ[2 + 2, (0 : Fin (2 + 3))].ι ≫ σ :=
  exists_fill_horn_left_of_isEquivalence σ₀ h

/-- `n = 3`: filling of `Λ[5, 0]` with the `(0, 1)`-edge an
equivalence. -/
example (σ₀ : (Λ[3 + 2, (0 : Fin (3 + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3 + 2] ⟶ X, σ₀ = Λ[3 + 2, (0 : Fin (3 + 3))].ι ≫ σ :=
  exists_fill_horn_left_of_isEquivalence σ₀ h

/-- Arbitrary `n`: filling of `Λ[n + 2, 0]` with the `(0, 1)`-edge
an equivalence, the exact statement of
`exists_fill_horn_left_of_isEquivalence`. -/
example {n : ℕ} (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ :=
  exists_fill_horn_left_of_isEquivalence σ₀ h

/-- The left half of the special-horn condition of
`SSet.HasSpecialOuterHornFilling` (`CoreKan.lean`) holds for
every quasicategory. -/
example :
    ∀ {n : ℕ} (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X),
      (leftHornEdge σ₀).IsEquivalence →
        ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ :=
  fun σ₀ h => exists_fill_horn_left_of_isEquivalence σ₀ h

end LeftDimensionChecks

section RightDimensionChecks

/-- `n = 0`: filling of `Λ[2, 2]` with the last edge an
equivalence, compare `exists_fill_horn_two_last_of_isEquivalence`
in `CoreKan.lean`. -/
example (σ₀ : (Λ[0 + 2, Fin.last (0 + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[0 + 2] ⟶ X, σ₀ = Λ[0 + 2, Fin.last (0 + 2)].ι ≫ σ :=
  exists_fill_horn_right_of_isEquivalence σ₀ h

/-- `n = 1`: filling of `Λ[3, 3]` with the last edge an
equivalence, compare the right half of packet T18. -/
example (σ₀ : (Λ[1 + 2, Fin.last (1 + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[1 + 2] ⟶ X, σ₀ = Λ[1 + 2, Fin.last (1 + 2)].ι ≫ σ :=
  exists_fill_horn_right_of_isEquivalence σ₀ h

/-- `n = 2`: filling of `Λ[4, 4]` with the last edge an
equivalence; the first right dimension not covered by packet
T18. -/
example (σ₀ : (Λ[2 + 2, Fin.last (2 + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[2 + 2] ⟶ X, σ₀ = Λ[2 + 2, Fin.last (2 + 2)].ι ≫ σ :=
  exists_fill_horn_right_of_isEquivalence σ₀ h

/-- `n = 3`: filling of `Λ[5, 5]` with the last edge an
equivalence. -/
example (σ₀ : (Λ[3 + 2, Fin.last (3 + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3 + 2] ⟶ X, σ₀ = Λ[3 + 2, Fin.last (3 + 2)].ι ≫ σ :=
  exists_fill_horn_right_of_isEquivalence σ₀ h

/-- Arbitrary `n`: filling of `Λ[n + 2, n + 2]` with the last
edge an equivalence, the exact statement of
`exists_fill_horn_right_of_isEquivalence`. -/
example {n : ℕ} (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ :=
  exists_fill_horn_right_of_isEquivalence σ₀ h

/-- The right half of the special-horn condition of
`SSet.HasSpecialOuterHornFilling` (`CoreKan.lean`) holds for
every quasicategory. -/
example :
    ∀ {n : ℕ} (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X),
      (rightHornEdge σ₀).IsEquivalence →
        ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ :=
  fun σ₀ h => exists_fill_horn_right_of_isEquivalence σ₀ h

/-- The opposite of a quasicategory is a quasicategory
(`SSet.quasicategory_op`), the transport used for right
horns. -/
example : Quasicategory X.op := quasicategory_op X

end RightDimensionChecks

section Corollaries

/-- Every quasicategory has special outer horn filling in the
sense of `CoreKan.lean`. -/
example : HasSpecialOuterHornFilling X :=
  hasSpecialOuterHornFilling_of_quasicategory X

/-- The two components of the special-horn filling property, via
the accessors of `CoreKan.lean`. -/
example {n : ℕ} (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ :=
  (hasSpecialOuterHornFilling_of_quasicategory X).left σ₀ h

example {n : ℕ} (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ :=
  (hasSpecialOuterHornFilling_of_quasicategory X).right σ₀ h

/-- The core of every quasicategory is a Kan complex, directly
and through the instance. -/
example : KanComplex (core X : SSet.{u}) :=
  kanComplex_core_of_quasicategory X

example : KanComplex (core X : SSet.{u}) := inferInstance

end Corollaries

section InstancePaths

variable [KanComplex Y]

/-- Under `[Quasicategory X]`, the core is a Kan complex by
instance search, through the general instance of
`SpecialOuterHornGeneral.lean`. -/
example : KanComplex (core X : SSet.{u}) := inferInstance

/-- Under `[KanComplex Y]`, the core is still a Kan complex by
instance search; the Kan-specialized instance of `CoreKan.lean`
has higher priority than the general quasicategory instance, so
the specialized route is the one found. -/
example : KanComplex (core Y : SSet.{u}) := inferInstance

/-- Both named routes apply under `[KanComplex Y]`: the
specialized theorem of `CoreKan.lean` and the general theorem
of `SpecialOuterHornGeneral.lean` (a Kan complex is a
quasicategory). -/
example : KanComplex (core Y : SSet.{u}) :=
  kanComplex_core_of_kanComplex Y

example : KanComplex (core Y : SSet.{u}) :=
  kanComplex_core_of_quasicategory Y

end InstancePaths

section AbstractCore

/-- The subset filtration concerns the set of tail vertices
`{2, ..., N + 2}`; this pins the order-embedding bookkeeping:
deleting two distinct positions commutes in the simplicial way,
and the embeddings `(0, 2, ..., N + 2)` and
`(0, 1, 2, ..., ĵ, ..., N + 2)` are the face embeddings. -/
example {k N : ℕ} (u : Fin (k + 2) ↪o Fin (N + 1))
    {j l : Fin (k + 2)} (hjl : j < l) :
    delEmb (delEmb u l) (j.castLT (by
      have h1 := l.isLt
      rw [Fin.lt_def] at hjl
      omega)) =
      delEmb (delEmb u j) (l.pred (Fin.ne_zero_of_lt hjl)) :=
  delEmb_delEmb u hjl

example {N : ℕ} :
    emb0 ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) =
      Fin.succAboveOrderEmb (1 : Fin (N + 3)) :=
  emb0_reflEmb

example {N : ℕ} (j : Fin (N + 1)) :
    emb01 (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) =
      Fin.succAboveOrderEmb j.succ.succ :=
  emb01_delEmb_reflEmb j

/-- The dual bookkeeping: the suffix embeddings
`(0, ..., N, N + 2)` and `(0, ..., ĵ, ..., N, N + 1, N + 2)` are
the face embeddings, and deletion commutes with reversal. -/
example {N : ℕ} :
    emb2r ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) =
      Fin.succAboveOrderEmb (Fin.last (N + 1)).castSucc :=
  emb2r_reflEmb

example {N : ℕ} (j : Fin (N + 1)) :
    emb12r (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) =
      Fin.succAboveOrderEmb j.castSucc.castSucc :=
  emb12r_delEmb_reflEmb j

example {k N : ℕ} (u : Fin (k + 1) ↪o Fin (N + 1)) (j : Fin (k + 1)) :
    delEmb (revEmb u) j.rev = revEmb (delEmb u j) :=
  delEmb_revEmb u j

end AbstractCore

end SSet

-- Only the standard axioms should appear (no `sorry`):
-- `propext`, `Classical.choice`, `Quotient.sound`.
#print axioms SSet.exists_fill_horn_left_of_isEquivalence
#print axioms SSet.exists_fill_horn_right_of_isEquivalence
#print axioms SSet.exists_filler_simplex_of_leftData
#print axioms SSet.hasSpecialOuterHornFilling_of_quasicategory
#print axioms SSet.kanComplex_core_of_quasicategory
