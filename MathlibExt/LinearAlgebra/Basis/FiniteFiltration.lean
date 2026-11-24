/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Bases adapted to a finite filtration

This file assembles bases of the successive quotients of an increasing
filtration into a basis of a finite filtration stage.  It also records the
chosen representative of every graded basis vector in the stage where that
vector is introduced.

## Main declarations

* `Module.Basis.FiltrationIndex` is the dependent sum of the graded basis
  indices below a finite cutoff.
* `Module.Basis.ofFiltrationStage` is the resulting basis of a finite
  filtration stage.
* `Module.Basis.ofFiltrationStageVector` regards a basis vector as an element
  of the stage where it is introduced.
* `Module.Basis.ofFiltration` specializes the construction when the final
  stage is the whole ambient module.

## Informal proof

Let `F 0 <= F 1 <= ...` be a filtration with `F 0 = 0`, and suppose that the
quotient `F (i+1) / F i` has a basis indexed by `kappa i`.  We argue by
induction on the cutoff `n`.

For `n = 0`, the stage `F 0` is the zero module, so its empty family is a
basis.  For the induction step, identify `F n` with its image as a submodule
of `F (n+1)`.  Mathlib's `Module.Basis.sumQuot` combines the transported basis
of this submodule with arbitrary representatives of the supplied basis of
`F (n+1) / F n`.  Its index type is the disjoint sum of the old indices and
`kappa n`; reindexing by the evident equivalence identifies this sum with
`Sigma i : Fin (n+1), kappa i`.

The `sumQuot_inl` formula says that every old vector is carried forward
without changing its ambient value.  The `sumQuot_inr` formula says that each
new vector maps to the prescribed quotient-basis vector.  Induction therefore
shows that every final basis vector still lies in the stage where it was
introduced and has exactly the prescribed image in the corresponding
successive quotient.  If the final stage is the top submodule, its canonical
linear equivalence with the ambient module transports this stage basis to a
basis of the ambient module without changing any underlying vector.
-/

@[expose] public section

universe u v w

namespace Module.Basis

variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M]

/-- The dependent sum of the graded basis indices strictly below `n`. -/
abbrev FiltrationIndex (κ : ℕ → Type w) (n : ℕ) :=
  Σ i : Fin n, κ i.val

/-- Add the last graded index to the dependent sum of the preceding indices. -/
def filtrationIndexSuccEquiv (κ : ℕ → Type w) (n : ℕ) :
    FiltrationIndex κ n ⊕ κ n ≃ FiltrationIndex κ (n + 1) where
  toFun
    | Sum.inl ⟨i, a⟩ => ⟨i.castSucc, a⟩
    | Sum.inr a => ⟨Fin.last n, a⟩
  invFun p :=
    Fin.lastCases (fun a => Sum.inr a)
      (fun i a => Sum.inl ⟨i, a⟩) p.1 p.2
  left_inv x := by
    rcases x with (⟨i, a⟩ | a)
    · simp
    · simp
  right_inv p := by
    rcases p with ⟨i, a⟩
    revert a
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro a
      simp
    · intro a
      simp

@[simp]
theorem filtrationIndexSuccEquiv_apply_inl
    (κ : ℕ → Type w) (n : ℕ) (i : Fin n) (a : κ i.val) :
    filtrationIndexSuccEquiv κ n (Sum.inl ⟨i, a⟩) = ⟨i.castSucc, a⟩ :=
  rfl

@[simp]
theorem filtrationIndexSuccEquiv_apply_inr
    (κ : ℕ → Type w) (n : ℕ) (a : κ n) :
    filtrationIndexSuccEquiv κ n (Sum.inr a) = ⟨Fin.last n, a⟩ :=
  rfl

@[simp]
theorem filtrationIndexSuccEquiv_symm_castSucc
    (κ : ℕ → Type w) (n : ℕ) (i : Fin n) (a : κ i.val) :
    (filtrationIndexSuccEquiv κ n).symm ⟨i.castSucc, a⟩ =
      Sum.inl ⟨i, a⟩ := by
  simp [filtrationIndexSuccEquiv]

@[simp]
theorem filtrationIndexSuccEquiv_symm_last
    (κ : ℕ → Type w) (n : ℕ) (a : κ n) :
    (filtrationIndexSuccEquiv κ n).symm ⟨Fin.last n, a⟩ =
      Sum.inr a := by
  simp [filtrationIndexSuccEquiv]

/-- A basis of a finite filtration stage assembled from bases of all its
successive quotients.

The filtration is indexed by natural numbers, while `n` selects the finite
segment used by this construction.  The result is indexed by the dependent
sum of the supplied graded basis indices. -/
noncomputable def ofFiltrationStage
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w) :
    ∀ n,
      (∀ i : Fin n, F i.val ≤ F (i.val + 1)) →
      (∀ i : Fin n,
        Basis (κ i.val) R
          (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype)) →
      Basis (FiltrationIndex κ n) R (F n)
  | 0, _, _ => by
      letI : Subsingleton (F 0) := by
        rw [hzero]
        infer_instance
      exact Basis.empty (F 0)
  | n + 1, hF, b =>
      let hF' : ∀ i : Fin n, F i.val ≤ F (i.val + 1) :=
        fun i => hF i.castSucc
      let b' : ∀ i : Fin n,
          Basis (κ i.val) R
            (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype) :=
        fun i => b i.castSucc
      let hlast : F n ≤ F (n + 1) := by
        simpa using hF (Fin.last n)
      let blast : Basis (κ n) R
          (F (n + 1) ⧸ (F n).comap (F (n + 1)).subtype) := by
        simpa using b (Fin.last n)
      let lower : Basis (FiltrationIndex κ n) R
          ((F n).comap (F (n + 1)).subtype) :=
        (ofFiltrationStage F hzero κ n hF' b').map
          (Submodule.comapSubtypeEquivOfLe hlast).symm
      (lower.sumQuot blast).reindex (filtrationIndexSuccEquiv κ n)

/-- Passing to the next filtration stage does not change an earlier basis
vector as an element of the ambient module. -/
@[simp]
theorem ofFiltrationStage_castSucc
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w)
    (n : ℕ) (hF : ∀ j : Fin (n + 1), F j.val ≤ F (j.val + 1))
    (b : ∀ j : Fin (n + 1),
      Basis (κ j.val) R
        (F (j.val + 1) ⧸ (F j.val).comap (F (j.val + 1)).subtype))
    (i : Fin n) (a : κ i.val) :
    ((ofFiltrationStage F hzero κ (n + 1) hF b
        ⟨i.castSucc, a⟩ : F (n + 1)) : M) =
      (ofFiltrationStage F hzero κ n (fun j => hF j.castSucc)
        (fun j => b j.castSucc) ⟨i, a⟩ : F n) := by
  simp [ofFiltrationStage]

/-- The vector added at the last step maps to the prescribed basis vector of
the last successive quotient. -/
@[simp]
theorem ofFiltrationStage_last_mk
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w)
    (n : ℕ)
    (hF : ∀ i : Fin (n + 1), F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin (n + 1),
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (a : κ n) :
    Submodule.Quotient.mk
        (ofFiltrationStage F hzero κ (n + 1) hF b ⟨Fin.last n, a⟩) =
      b (Fin.last n) a := by
  simp [ofFiltrationStage]

/-- Every assembled basis vector belongs to the filtration stage where its
graded index is introduced. -/
theorem ofFiltrationStage_mem
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w)
    (n : ℕ) (hF : ∀ j : Fin n, F j.val ≤ F (j.val + 1))
    (b : ∀ j : Fin n,
      Basis (κ j.val) R
        (F (j.val + 1) ⧸ (F j.val).comap (F (j.val + 1)).subtype))
    (i : Fin n) (a : κ i.val) :
    ((ofFiltrationStage F hzero κ n hF b ⟨i, a⟩ : F n) : M) ∈
      F (i.val + 1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      revert a
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro a
        exact (ofFiltrationStage F hzero κ (n + 1) hF b
          ⟨Fin.last n, a⟩).property
      · intro a
        rw [ofFiltrationStage_castSucc]
        exact ih (fun k => hF k.castSucc) (fun k => b k.castSucc) j a

/-- An assembled basis vector, restricted to the filtration stage where it
is introduced. -/
noncomputable def ofFiltrationStageVector
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (i : Fin n) (a : κ i.val) : F (i.val + 1) :=
  ⟨ofFiltrationStage F hzero κ n hF b ⟨i, a⟩,
    ofFiltrationStage_mem F hzero κ n hF b i a⟩

/-- Every assembled filtration vector is an exact representative of the
supplied basis vector in its successive quotient. -/
@[simp]
theorem ofFiltrationStageVector_mk
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (i : Fin n) (a : κ i.val) :
    Submodule.Quotient.mk
        (ofFiltrationStageVector F hzero κ n hF b i a) = b i a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      revert a
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro a
        simp [ofFiltrationStageVector]
      · intro a
        simpa [ofFiltrationStageVector] using
          ih (fun k => hF k.castSucc) (fun k => b k.castSucc) j a

/-- A basis of the ambient module assembled from bases of the successive
quotients of a finite filtration from zero to the top submodule. -/
noncomputable def ofFiltration
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤) : Basis (FiltrationIndex κ n) R M :=
  (ofFiltrationStage F hzero κ n hF b).map
    ((LinearEquiv.ofEq (F n) ⊤ htop).trans Submodule.topEquiv)

/-- Mapping the final filtration stage to the ambient module does not change
the underlying basis vectors. -/
@[simp]
theorem ofFiltration_apply
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥) (κ : ℕ → Type w)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤) (p : FiltrationIndex κ n) :
    ofFiltration F hzero κ n hF b htop p =
      (ofFiltrationStage F hzero κ n hF b p : F n) := by
  simp [ofFiltration]

end Module.Basis
