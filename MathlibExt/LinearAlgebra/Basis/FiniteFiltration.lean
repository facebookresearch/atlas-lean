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

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). These bases preserve
earlier vectors on passage to a larger stage. If F_n=M they give a basis of M. The graded
basis index sets may be infinite.
-/

@[expose] public section

universe u v w

namespace Module.Basis

variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M]

/-- **Index set for a finite filtration basis.**

For κ:ℕ→Type and n∈ℕ, FiltrationIndex κ n=Σi:Fin n,κ_i, the disjoint union of the graded
indices below n.
-/
abbrev FiltrationIndex (κ : ℕ → Type w) (n : ℕ) :=
  Σ i : Fin n, κ i.val

/-- **Adding the last graded index.**

For κ:ℕ→Type and n∈ℕ, filtrationIndexSuccEquiv:(Σ_{i<n}κ_i)⊕κ_n≃Σ_{i<n+1}κ_i includes earlier
indices and sends a∈κ_n to (n,a).
-/
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

/-- **Basis assembled on a finite filtration stage.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). The constructor
ofFiltrationStage F hzero κ n hF b is the basis B_n of F_n.
-/
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

/-- **Earlier filtration basis vectors retain their ambient values.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). Using one chain and its
quotient bases through stage n+1, B_(n+1)(i,a)=B_n(i,a) in M whenever i<n.
-/
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

/-- **Last-stage vector has the specified graded basis image.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). At stage n+1, the image
of B_(n+1)(n,a) in F_(n+1)/F_n is b_n(a).
-/
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

/-- **A filtration basis vector lies in its introduction stage.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). For i<n and a∈κ_i, the
ambient vector of ofFiltrationStage(i,a) belongs to F_(i+1).
-/
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

/-- **Introduced filtration vector in its own stage.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). The value
ofFiltrationStageVector F hzero κ n hF b i a is B_n(i,a), regarded as a vector of F_(i+1).
-/
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

/-- **Introduced vector represents its graded basis element.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). The image of
ofFiltrationStageVector(i,a) in F_(i+1)/F_i equals b_i(a).
-/
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

/-- **Ambient basis from a filtration ending at the whole module.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). If F_n=M, ofFiltration
F hzero κ n hF b htop gives the basis of M indexed by Σ_{i<n}κ_i.
-/
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

/-- **Ambient filtration basis has the same stage vectors.**

Let R be a commutative ring, M an R-module, F_i⊆M a chain for i=0,…,n with F_0=0, and b_i a
basis indexed by κ_i of F_(i+1)/F_i for i<n. The stage basis B_n of F_n is indexed by
Σ_{i<n}κ_i; its vector B_n(i,a) lies in F_(i+1) and represents b_i(a). If F_n=M, the vector of
ofFiltration at (i,a) equals B_n(i,a) viewed from F_n in M.
-/
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
