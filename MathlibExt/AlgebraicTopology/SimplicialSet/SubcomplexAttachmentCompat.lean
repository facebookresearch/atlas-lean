/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Monotone.Basic

/-!
# Boundary attachments between simplicial subcomplexes

Let A < J be subcomplexes of a simplicial set X. Choose a nondegenerate simplex x of J outside
A of minimal dimension n. Every lower-dimensional nondegenerate simplex of J lies in A, so the
boundary of x maps into A. The subcomplex B = A ⊔ ofSimplex(x) satisfies A < B ≤ J.

There is a pushout square with edges ∂Δ[n] → A, ∂Δ[n] → Δ[n], A → B and Δ[n] → B. The witness
version retains x, its membership and minimality, and the join description of B. If A ≤ J and
J is finite, these attachments give a finite monotone chain from A to J, each successive step
strict and carrying its boundary pushout data. The ambient simplicial-set universe is
arbitrary.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial SSet Opposite

namespace SSet
namespace boundary

private def relMissingPred (X : SSet.{u}) (A J : X.Subcomplex) (n : ℕ) : Prop :=
  ∃ x : X.nonDegenerate n,
    x.1 ∈ J.obj (Opposite.op ⦋n⦌) ∧ x.1 ∉ A.obj (Opposite.op ⦋n⦌)

private lemma exists_relMissing_of_lt {X : SSet.{u}} {A J : X.Subcomplex}
    (h : A < J) : ∃ n, relMissingPred X A J n := by
  by_contra hnone
  simp only [not_exists] at hnone
  have hJA : J ≤ A := by
    apply (Subcomplex.le_iff_contains_nonDegenerate J A).mpr
    intro n x hxJ
    by_contra hxA
    exact hnone n ⟨x, hxJ, hxA⟩
  exact (ne_of_lt h) (le_antisymm h.le hJA)

private lemma boundary_mem_iff_notEpi {n d : ℕ}
    (s : (Δ[n] : SSet.{u}).obj (Opposite.op ⦋d⦌)) :
    s ∈ (SSet.boundary n).obj (Opposite.op ⦋d⦌) ↔
      ¬Epi (SSet.stdSimplex.objEquiv s) := by
  rw [SSet.boundary]
  simp only [Set.mem_ofPred_eq]
  rw [SimplexCategory.epi_iff_surjective]
  have h : Function.Surjective (SSet.stdSimplex.asOrderHom (n := n) (m := Opposite.op ⦋d⦌) s) ↔
      Function.Surjective (SSet.stdSimplex.objEquiv s).toOrderHom := by
    rfl
  exact h.not

/-- Shared construction: attach a minimal-dimensional nondegenerate simplex of `J`
missing from `A` via a pushout from `∂Δ[n₀]`, yielding `A < B` with `B ≤ J`. -/
private lemma pushout_of_minimal_relMissing {X : SSet.{u}} {A J : X.Subcomplex}
    (hAJ : A ≤ J) {n₀ : ℕ} {x₀ : X.nonDegenerate n₀}
    (hxJ : x₀.1 ∈ J.obj (Opposite.op ⦋n₀⦌))
    (hx₀ : x₀.1 ∉ A.obj (Opposite.op ⦋n₀⦌))
    (hMin : ∀ m, m < n₀ → ∀ y : X.nonDegenerate m,
      y.1 ∈ J.obj (Opposite.op ⦋m⦌) → y.1 ∈ A.obj (Opposite.op ⦋m⦌)) :
    ∃ (B : X.Subcomplex) (hAB : A < B) (_ : B ≤ J)
      (_ : B = A ⊔ Subcomplex.ofSimplex x₀.1)
      (t : (SSet.boundary n₀ : SSet.{u}) ⟶ (A : SSet.{u}))
      (b : (Δ[n₀] : SSet.{u}) ⟶ (B : SSet.{u})),
      IsPushout t (SSet.boundary n₀).ι (SSet.Subcomplex.homOfLE hAB.le) b := by
  classical
  let xn : X _⦋n₀⦌ := x₀.1
  let f₀ : Δ[n₀] ⟶ X := SSet.yonedaEquiv.symm xn
  have hPre : A.preimage f₀ = SSet.boundary n₀ := by
    ext ⟨⟨m⟩⟩ s
    simp only [SSet.Subcomplex.preimage_obj, Set.mem_preimage]
    have hf_eq : f₀.app (Opposite.op ⦋m⦌) s = X.map (SSet.stdSimplex.objEquiv s).op xn := rfl
    constructor
    · intro hs
      rw [hf_eq] at hs
      by_contra hNotMem
      have hEpi : Epi (SSet.stdSimplex.objEquiv s) := by
        by_contra hNotEpi
        have hMem : s ∈ (SSet.boundary n₀).obj (Opposite.op ⦋m⦌) := by
          rw [boundary_mem_iff_notEpi]
          exact hNotEpi
        exact hNotMem hMem
      have hEpiInst : Epi (SSet.stdSimplex.objEquiv s) := hEpi
      have hEq : Subcomplex.ofSimplex (X.map (SSet.stdSimplex.objEquiv s).op xn) =
          Subcomplex.ofSimplex xn :=
        @Subcomplex.ofSimplex_map_of_epi _ _ _ (SSet.stdSimplex.objEquiv s) hEpiInst xn
      have hLe : Subcomplex.ofSimplex xn ≤ A := by
        rw [← hEq, Subcomplex.ofSimplex_le_iff]
        exact hs
      exact hx₀ ((Subcomplex.ofSimplex_le_iff _ _).mp hLe)
    · intro hs
      rw [hf_eq]
      have hNotEpi : ¬Epi (SSet.stdSimplex.objEquiv s) :=
        (boundary_mem_iff_notEpi s).mp hs
      have hFac : SSet.stdSimplex.objEquiv s =
          factorThruImage (SSet.stdSimplex.objEquiv s) ≫
            image.ι (SSet.stdSimplex.objEquiv s) :=
        (image.fac (SSet.stdSimplex.objEquiv s)).symm
      have hMono : Mono (image.ι (SSet.stdSimplex.objEquiv s)) :=
        inferInstance
      have hNotIso : ¬IsIso (image.ι (SSet.stdSimplex.objEquiv s)) := by
        intro hIso
        have : Epi (SSet.stdSimplex.objEquiv s) := by
          rw [hFac]
          infer_instance
        exact hNotEpi this
      have hLenMono : (image (SSet.stdSimplex.objEquiv s)).len ≤ n₀ :=
        SimplexCategory.len_le_of_mono (image.ι _)
      have hLenLt : (image (SSet.stdSimplex.objEquiv s)).len < n₀ := by
        by_contra hle
        simp only [not_lt] at hle
        have heq : (image (SSet.stdSimplex.objEquiv s)).len = n₀ :=
          le_antisymm hLenMono hle
        have hIsIso : IsIso (image.ι (SSet.stdSimplex.objEquiv s)) := by
          rw [SimplexCategory.isIso_iff_of_mono]
          exact heq
        exact hNotIso hIsIso
      have hFace : X.map (image.ι (SSet.stdSimplex.objEquiv s)).op xn ∈
          A.obj (Opposite.op ⦋(image (SSet.stdSimplex.objEquiv s)).len⦌) := by
        obtain ⟨l, e, _, z, hz⟩ := X.exists_nonDegenerate
            (X.map (image.ι (SSet.stdSimplex.objEquiv s)).op xn)
        have hl_le : l ≤ (image (SSet.stdSimplex.objEquiv s)).len :=
          SimplexCategory.len_le_of_epi e
        have hl_lt : l < n₀ := Nat.lt_of_le_of_lt hl_le hLenLt
        have hwJ : X.map (image.ι (SSet.stdSimplex.objEquiv s)).op xn ∈
            J.obj (Opposite.op ⦋(image (SSet.stdSimplex.objEquiv s)).len⦌) :=
          J.map (image.ι (SSet.stdSimplex.objEquiv s)).op hxJ
        have hzJ_mem : X.map e.op z.1 ∈
            J.obj (Opposite.op ⦋(image (SSet.stdSimplex.objEquiv s)).len⦌) := hz ▸ hwJ
        have hOfJ : Subcomplex.ofSimplex (X.map e.op z.1) ≤ J :=
          (Subcomplex.ofSimplex_le_iff _ _).mpr hzJ_mem
        rw [Subcomplex.ofSimplex_map_of_epi e z.1] at hOfJ
        have hzJ : z.1 ∈ J.obj (Opposite.op ⦋l⦌) :=
          (Subcomplex.ofSimplex_le_iff _ _).mp hOfJ
        have hzA : z.1 ∈ A.obj (Opposite.op ⦋l⦌) := hMin l hl_lt z hzJ
        have h1 : X.map e.op z.1 ∈
            A.obj (Opposite.op ⦋(image (SSet.stdSimplex.objEquiv s)).len⦌) := by
          have hsub : A.obj (Opposite.op ⦋l⦌) ⊆
              X.map e.op ⁻¹' A.obj (Opposite.op ⦋(image (SSet.stdSimplex.objEquiv s)).len⦌) :=
            A.map e.op
          exact hsub hzA
        -- hz : X.map (image.ι).op xn = X.map e.op z.1 from exists_nonDegenerate
        have hz_symm : X.map e.op z.1 = X.map (image.ι (SSet.stdSimplex.objEquiv s)).op xn :=
          hz.symm
        -- keep equality explicitly
        have : X.map (image.ι (SSet.stdSimplex.objEquiv s)).op xn ∈
            A.obj (Opposite.op ⦋(image (SSet.stdSimplex.objEquiv s)).len⦌) := by
          rw [← hz] at h1
          -- use ← hz to turn RHS membership into LHS membership
          exact h1
        exact this
      have hMem : X.map (SSet.stdSimplex.objEquiv s).op xn ∈
          A.obj (Opposite.op ⦋m⦌) := by
        have hf_op : (SSet.stdSimplex.objEquiv s).op =
            (factorThruImage (SSet.stdSimplex.objEquiv s) ≫
              image.ι (SSet.stdSimplex.objEquiv s)).op :=
          congrArg (·.op) hFac
        have h1 : (SSet.stdSimplex.objEquiv s).op =
            (image.ι (SSet.stdSimplex.objEquiv s)).op ≫
              (factorThruImage (SSet.stdSimplex.objEquiv s)).op :=
          hf_op.trans op_comp
        have hCompEq : X.map (SSet.stdSimplex.objEquiv s).op xn =
            X.map (factorThruImage (SSet.stdSimplex.objEquiv s)).op
              (X.map (image.ι (SSet.stdSimplex.objEquiv s)).op xn) := by
          rw [h1, Functor.map_comp]
          rfl
        have hSub : A.obj (Opposite.op ⦋(image (SSet.stdSimplex.objEquiv s)).len⦌) ⊆
            X.map (factorThruImage (SSet.stdSimplex.objEquiv s)).op ⁻¹'
              A.obj (Opposite.op ⦋m⦌) :=
          A.map (factorThruImage (SSet.stdSimplex.objEquiv s)).op
        have h2 : X.map (factorThruImage (SSet.stdSimplex.objEquiv s)).op
            (X.map (image.ι (SSet.stdSimplex.objEquiv s)).op xn) ∈
            A.obj (Opposite.op ⦋m⦌) :=
          hSub hFace
        rw [← hCompEq] at h2
        exact h2
      exact hMem
  let B : X.Subcomplex := A ⊔ Subcomplex.ofSimplex xn
  have hA_le_B : A ≤ B := le_sup_left
  have hA_ne_B : A ≠ B := by
    intro heq
    have : xn ∈ A.obj (Opposite.op ⦋n₀⦌) := by
      have : xn ∈ B.obj (Opposite.op ⦋n₀⦌) := by
        simp only [B, Subfunctor.max_obj]
        exact Set.mem_union_right _ (Subcomplex.mem_ofSimplex_obj xn)
      rw [← heq] at this
      exact this
    exact hx₀ this
  have hlt : A < B := lt_of_le_of_ne hA_le_B hA_ne_B
  have hOfLe : Subcomplex.ofSimplex xn ≤ J :=
    (Subcomplex.ofSimplex_le_iff _ _).mpr hxJ
  have hBJ : B ≤ J := sup_le hAJ hOfLe
  have hRangeLeA : Subcomplex.range ((SSet.boundary n₀).ι ≫ f₀) ≤ A := by
    rw [← Subcomplex.preimage_eq_top_iff]
    rw [Subcomplex.preimage_comp]
    rw [hPre]
    simp [Subcomplex.preimage_ι]
  let t : (SSet.boundary n₀ : SSet.{u}) ⟶ (A : SSet.{u}) :=
    Subcomplex.lift ((SSet.boundary n₀).ι ≫ f₀) hRangeLeA
  have hRangeLeB : Subcomplex.range f₀ ≤ B := by
    rw [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
    exact le_sup_right
  let b : (Δ[n₀] : SSet.{u}) ⟶ (B : SSet.{u}) :=
    Subcomplex.lift f₀ hRangeLeB
  have hw : t ≫ Subcomplex.homOfLE hlt.le = (SSet.boundary n₀).ι ≫ b := by
    apply (cancel_mono (B.ι)).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.lift_ι, t, b]
  have hIsPushout : IsPushout t (SSet.boundary n₀).ι (Subcomplex.homOfLE hlt.le) b := {
    w := hw
    isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨m⟩⟩ => by
      let e : SimplexCategoryᵒᵖ := Opposite.op ⦋m⦌
      have hWapp : t.app e ≫ (Subcomplex.homOfLE hlt.le).app e =
          (SSet.boundary n₀).ι.app e ≫ b.app e := congr_app hw e
      apply (isColimitMapCoconePushoutCoconeEquiv (SSet.evaluation.obj e) _).2
      apply IsPushout.isColimit
      have hMonoHom : Mono ((Subcomplex.homOfLE hlt.le).app e) := by
        rw [mono_iff_injective]
        intro a₁ a₂ hEq
        have : a₁.val = a₂.val := by
          calc a₁.val = ((Subcomplex.homOfLE hlt.le).app e a₁).val := rfl
            _ = ((Subcomplex.homOfLE hlt.le).app e a₂).val := congrArg Subtype.val hEq
            _ = a₂.val := rfl
        exact Subtype.ext this
      have hPull : IsPullback
          (t.app e) ((SSet.boundary n₀).ι.app e)
          ((Subcomplex.homOfLE hlt.le).app e) (b.app e) := by
        rw [CategoryTheory.Limits.Types.isPullback_iff]
        refine ⟨hWapp, ?_, ?_⟩
        · intro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ ⟨_, h2⟩
          dsimp at h2
          exact Subtype.ext h2
        · intro a₂ a₃ heq
          have hb_eq : (b.app e a₃).val =
              X.map (SSet.stdSimplex.objEquiv a₃).op xn := rfl
          have ha_eq : a₂.val = X.map (SSet.stdSimplex.objEquiv a₃).op xn := by
            calc a₂.val = ((Subcomplex.homOfLE hlt.le).app e a₂).val := rfl
              _ = (b.app e a₃).val := congrArg Subtype.val heq
              _ = X.map (SSet.stdSimplex.objEquiv a₃).op xn := hb_eq
          have hf_notEpi : ¬Epi (SSet.stdSimplex.objEquiv a₃) := by
            intro hEpi
            have hEpiInst : Epi (SSet.stdSimplex.objEquiv a₃) := hEpi
            have hEq : Subcomplex.ofSimplex (X.map (SSet.stdSimplex.objEquiv a₃).op xn) =
                Subcomplex.ofSimplex xn :=
              @Subcomplex.ofSimplex_map_of_epi _ _ _
                (SSet.stdSimplex.objEquiv a₃) hEpiInst xn
            have hLe : Subcomplex.ofSimplex xn ≤ A := by
              rw [← hEq, Subcomplex.ofSimplex_le_iff, ← ha_eq]
              exact a₂.2
            exact hx₀ ((Subcomplex.ofSimplex_le_iff _ _).mp hLe)
          have hm : a₃ ∈ (SSet.boundary n₀).obj e := by
            rw [boundary_mem_iff_notEpi]
            exact hf_notEpi
          refine ⟨⟨a₃, hm⟩, ?_, ?_⟩
          · apply Subtype.ext
            calc (t.app e ⟨a₃, hm⟩).val = X.map (SSet.stdSimplex.objEquiv a₃).op xn := rfl
              _ = a₂.val := ha_eq.symm
          · rfl
      have hSup : Set.range ((Subcomplex.homOfLE hlt.le).app e) ⊔
          Set.range (b.app e) = Set.univ := by
        have : Set.range ((Subcomplex.homOfLE hlt.le).app e) ⊔
            Set.range (b.app e) =
            Set.range ((Subcomplex.homOfLE hlt.le).app e) ∪
            Set.range (b.app e) := rfl
        rw [this, Set.eq_univ_iff_forall]
        intro ⟨y, hy⟩
        by_cases hAy : y ∈ A.obj e
        · exact Or.inl ⟨⟨y, hAy⟩, Subtype.ext rfl⟩
        · have hBy : y ∈ B.obj e := hy
          simp only [B, Subfunctor.max_obj, Set.mem_union] at hBy
          rcases hBy with h | h
          · exact absurd h hAy
          · obtain ⟨f, rfl⟩ := (Subcomplex.mem_ofSimplex_obj_iff _ _).mp h
            exact Or.inr ⟨SSet.stdSimplex.objEquiv.symm f, Subtype.ext rfl⟩
      refine @CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono' _ _ _ _ _ _ _ _
          hPull hMonoHom hSup ?_
      intro s₁ s₂ hs₁ hs₂ heq
      have hEpi1 : Epi (SSet.stdSimplex.objEquiv s₁) := by
        by_contra hNotEpi
        have : s₁ ∈ (SSet.boundary n₀).obj e := by
          rwa [boundary_mem_iff_notEpi]
        exact hs₁ ⟨⟨s₁, this⟩, rfl⟩
      have hEpi2 : Epi (SSet.stdSimplex.objEquiv s₂) := by
        by_contra hNotEpi
        have : s₂ ∈ (SSet.boundary n₀).obj e := by
          rwa [boundary_mem_iff_notEpi]
        exact hs₂ ⟨⟨s₂, this⟩, rfl⟩
      have hEq : X.map (SSet.stdSimplex.objEquiv s₁).op xn =
          X.map (SSet.stdSimplex.objEquiv s₂).op xn := by
        have := congrArg Subtype.val heq
        exact this
      have hF_eq : SSet.stdSimplex.objEquiv s₁ = SSet.stdSimplex.objEquiv s₂ :=
        @SSet.unique_nonDegenerate_map _ _ _ _ (SSet.stdSimplex.objEquiv s₁) hEpi1
          ⟨xn, x₀.2⟩ rfl (SSet.stdSimplex.objEquiv s₂) ⟨xn, x₀.2⟩ hEq
      exact congrArg SSet.stdSimplex.objEquiv.symm hF_eq
      )⟩
  }
  exact ⟨B, hlt, hBJ, rfl, t, b, hIsPushout⟩

/-- One boundary attachment inside a larger subcomplex.

For subcomplexes A < J of X, there exist B with A < B ≤ J, a natural dimension n and maps t :
∂Δ[n] → A, b : Δ[n] → B such that the square (t,boundary inclusion,A → B,b) is a pushout. The
construction attaches a minimal-dimensional nondegenerate simplex of J missing from A. -/
theorem exists_isPushout_of_lt {X : SSet.{u}} (A J : X.Subcomplex) (h : A < J) :
    ∃ (B : X.Subcomplex) (hAB : A < B) (_ : B ≤ J) (n : ℕ)
      (t : (SSet.boundary n : SSet.{u}) ⟶ (A : SSet.{u}))
      (b : (Δ[n] : SSet.{u}) ⟶ (B : SSet.{u})),
      IsPushout t (SSet.boundary n).ι (SSet.Subcomplex.homOfLE hAB.le) b := by
  classical
  have hAJ : A ≤ J := h.le
  have hExists : ∃ n, relMissingPred X A J n := exists_relMissing_of_lt h
  let n₀ := Nat.find hExists
  have hP_n₀ : relMissingPred X A J n₀ := Nat.find_spec hExists
  obtain ⟨x₀, hxJ, hx₀⟩ := hP_n₀
  have hMin : ∀ m, m < n₀ → ∀ y : X.nonDegenerate m,
      y.1 ∈ J.obj (Opposite.op ⦋m⦌) → y.1 ∈ A.obj (Opposite.op ⦋m⦌) := by
    intro m hm y hyJ
    by_contra hyA
    exact Nat.find_min hExists hm ⟨y, hyJ, hyA⟩
  obtain ⟨B, hAB, hBJ, _, t, b, hPush⟩ :=
    pushout_of_minimal_relMissing hAJ hxJ hx₀ hMin
  exact ⟨B, hAB, hBJ, n₀, t, b, hPush⟩

/-- Boundary attachment with a minimal nondegenerate witness.

For A < J, choose x ∈ J_n nondegenerate and outside A, with every nondegenerate simplex of J
in smaller dimension lying in A. Then B = A ⊔ ofSimplex(x) satisfies A < B ≤ J and is the
pushout of ∂Δ[n] → A along ∂Δ[n] → Δ[n]. The result retains x, both membership conditions,
minimality and the join equality. -/
theorem exists_isPushout_of_lt_with_witness {X : SSet.{u}} (A J : X.Subcomplex)
    (h : A < J) :
    ∃ (B : X.Subcomplex) (hAB : A < B) (_ : B ≤ J) (n : ℕ)
      (x : X.nonDegenerate n)
      (_hxJ : x.1 ∈ J.obj (Opposite.op ⦋n⦌))
      (_hxA : x.1 ∉ A.obj (Opposite.op ⦋n⦌))
      (_hMin : ∀ m, m < n → ∀ y : X.nonDegenerate m,
        y.1 ∈ J.obj (Opposite.op ⦋m⦌) → y.1 ∈ A.obj (Opposite.op ⦋m⦌))
      (_hJoin : B = A ⊔ Subcomplex.ofSimplex x.1)
      (t : (SSet.boundary n : SSet.{u}) ⟶ (A : SSet.{u}))
      (b : (Δ[n] : SSet.{u}) ⟶ (B : SSet.{u})),
      IsPushout t (SSet.boundary n).ι (SSet.Subcomplex.homOfLE hAB.le) b := by
  classical
  have hAJ : A ≤ J := h.le
  have hExists : ∃ n, relMissingPred X A J n := exists_relMissing_of_lt h
  let n₀ := Nat.find hExists
  have hP_n₀ : relMissingPred X A J n₀ := Nat.find_spec hExists
  obtain ⟨x₀, hxJ, hx₀⟩ := hP_n₀
  have hMin : ∀ m, m < n₀ → ∀ y : X.nonDegenerate m,
      y.1 ∈ J.obj (Opposite.op ⦋m⦌) → y.1 ∈ A.obj (Opposite.op ⦋m⦌) := by
    intro m hm y hyJ
    by_contra hyA
    exact Nat.find_min hExists hm ⟨y, hyJ, hyA⟩
  obtain ⟨B, hAB, hBJ, hJoin, t, b, hPush⟩ :=
    pushout_of_minimal_relMissing hAJ hxJ hx₀ hMin
  exact ⟨B, hAB, hBJ, n₀, x₀, hxJ, hx₀, hMin, hJoin, t, b, hPush⟩

/-- Boundary attachment to a proper simplicial subcomplex.

For A ≠ ⊤ in X, there exist B with A < B, a dimension n and a pushout square ∂Δ[n] → A, ∂Δ[n]
→ Δ[n], A → B and Δ[n] → B. This is the attachment inside J = ⊤. -/
theorem exists_isPushout_of_ne_top {X : SSet.{u}} (A : X.Subcomplex) (hA : A ≠ ⊤) :
    ∃ (B : X.Subcomplex) (lt : A < B) (n : ℕ)
      (t : (SSet.boundary n : SSet.{u}) ⟶ (A : SSet.{u}))
      (b : (Δ[n] : SSet.{u}) ⟶ (B : SSet.{u})),
      IsPushout t (SSet.boundary n).ι (SSet.Subcomplex.homOfLE lt.le) b := by
  have hLT : A < ⊤ := lt_of_le_of_ne le_top hA
  obtain ⟨B, hAB, _, n, t, b, hPush⟩ := exists_isPushout_of_lt A ⊤ hLT
  exact ⟨B, hAB, n, t, b, hPush⟩

/-- Finite boundary-attachment chain inside a finite subcomplex.

If A ≤ J and J is finite as a simplicial set, there exist k : ℕ and a monotone family C₀,…,C_k
with C₀=A and C_k=J. For every i<k, C_i<C_{i+1}≤J and the inclusion C_i→C_{i+1} is obtained by
a pushout of one standard simplex boundary. The case A=J allows k=0. -/
theorem exists_finite_attachment_chain_of_le_of_finite {X : SSet.{u}}
    (A J : X.Subcomplex) (hAJ : A ≤ J) [SSet.Finite (J : SSet.{u})] :
    ∃ (k : ℕ) (C : Fin (k + 1) → X.Subcomplex),
      C ⟨0, Nat.zero_lt_succ k⟩ = A ∧
      C ⟨k, Nat.lt_succ_self k⟩ = J ∧
      (∀ i j : Fin (k + 1), i.val ≤ j.val → C i ≤ C j) ∧
      ∀ (i : ℕ) (h : i < k),
        ∃ (n : ℕ)
          (t : (SSet.boundary n : SSet.{u}) ⟶
            ((C ⟨i, Nat.lt_trans h (Nat.lt_succ_self k)⟩ : X.Subcomplex) : SSet.{u}))
          (b : (Δ[n] : SSet.{u}) ⟶
            ((C ⟨i + 1, Nat.succ_lt_succ h⟩ : X.Subcomplex) : SSet.{u}))
          (hle : C ⟨i, Nat.lt_trans h (Nat.lt_succ_self k)⟩ ≤
            C ⟨i + 1, Nat.succ_lt_succ h⟩),
          IsPushout t (SSet.boundary n).ι (SSet.Subcomplex.homOfLE hle) b ∧
          C ⟨i, Nat.lt_trans h (Nat.lt_succ_self k)⟩ <
            C ⟨i + 1, Nat.succ_lt_succ h⟩ ∧
          C ⟨i + 1, Nat.succ_lt_succ h⟩ ≤ J := by
  classical
  have : Fintype (J : SSet.{u}).N := Fintype.ofFinite _
  have H : ∀ (c : ℕ) (B : X.Subcomplex), A ≤ B → B ≤ J →
      Fintype.card {s : (J : SSet.{u}).N // s.simplex.val ∉ B.obj _} = c →
      ∃ (k : ℕ) (f : ℕ → X.Subcomplex),
        f 0 = B ∧ f k = J ∧ (∀ i, f i ≤ f (i + 1)) ∧
        ∀ (i : ℕ), i < k →
          ∃ (n : ℕ)
            (t : (SSet.boundary n : SSet.{u}) ⟶ ((f i : X.Subcomplex) : SSet.{u}))
            (b : (Δ[n] : SSet.{u}) ⟶ ((f (i + 1) : X.Subcomplex) : SSet.{u}))
            (hle : f i ≤ f (i + 1)),
            IsPushout t (SSet.boundary n).ι (SSet.Subcomplex.homOfLE hle) b ∧
            f i < f (i + 1) ∧ f (i + 1) ≤ J := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro B hAB hBJ hc
      by_cases hBJ' : B = J
      · refine ⟨0, fun _ => J, ?_, rfl, ?_, ?_⟩
        · exact hBJ'.symm
        · intro i
          exact le_refl _
        · intro i h
          exact absurd h (Nat.not_lt_zero _)
      · have hBJlt : B < J := lt_of_le_of_ne hBJ hBJ'
        obtain ⟨B', hBB'lt, hB'J, n0, t0, b0, hPush0⟩ :=
          exists_isPushout_of_lt B J hBJlt
        have hBB' : B ≤ B' := hBB'lt.le
        obtain ⟨m, y, hyB', hyB⟩ := exists_relMissing_of_lt hBB'lt
        have hxJ : y.1 ∈ J.obj (Opposite.op ⦋m⦌) := hB'J _ hyB'
        let jx : (J : SSet.{u}) _⦋m⦌ := ⟨y.1, hxJ⟩
        have hxJT : jx ∈ SSet.nonDegenerate (J : SSet.{u}) m :=
          (SSet.Subcomplex.mem_nonDegenerate_iff J jx).mpr y.2
        let s0 : (J : SSet.{u}).N := SSet.N.mk jx hxJT
        have hs0B : s0.simplex.val ∉ B.obj _ := hyB
        have hs0B' : s0.simplex.val ∈ B'.obj _ := hyB'
        have hcard : Fintype.card {s : (J : SSet.{u}).N // s.simplex.val ∉ B'.obj _} <
            Fintype.card {s : (J : SSet.{u}).N // s.simplex.val ∉ B.obj _} := by
          apply Fintype.card_lt_of_injective_not_surjective
            (f := fun s => ⟨s.val, fun h => s.property (hBB' _ h)⟩)
          · intro s1 s2 h
            have hval : s1.val = s2.val := congrArg (fun s => s.val) h
            exact Subtype.ext hval
          · intro hSurj
            obtain ⟨s, hs⟩ := hSurj ⟨s0, hs0B⟩
            have hval : s.val = s0 := congrArg Subtype.val hs
            have hcontra : s.val.simplex.val ∉ B'.obj _ := s.property
            rw [hval] at hcontra
            exact hcontra hs0B'
        rw [hc] at hcard
        obtain ⟨k', f', hf'0, hf'k', hsucc', hstep'⟩ :=
          ih _ hcard B' (hAB.trans hBB') hB'J rfl
        let f : ℕ → X.Subcomplex := fun i => match i with
          | Nat.zero => B
          | Nat.succ n => f' n
        refine ⟨Nat.succ k', f, rfl, ?_, ?_, ?_⟩
        · exact hf'k'
        · intro i
          cases i with
          | zero =>
            change B ≤ f' Nat.zero
            exact hf'0.symm ▸ hBB'
          | succ n =>
            change f' n ≤ f' (n + 1)
            exact hsucc' n
        · intro i hi
          cases i with
          | zero =>
            change ∃ (n : ℕ)
                (t : (SSet.boundary n : SSet.{u}) ⟶ ((B : X.Subcomplex) : SSet.{u}))
                (b : (Δ[n] : SSet.{u}) ⟶ ((f' Nat.zero : X.Subcomplex) : SSet.{u}))
                (hle : B ≤ f' Nat.zero),
              IsPushout t (SSet.boundary n).ι (SSet.Subcomplex.homOfLE hle) b ∧
                B < f' Nat.zero ∧ f' Nat.zero ≤ J
            rw [hf'0]
            exact ⟨n0, t0, b0, hBB'lt.le, hPush0, hBB'lt, hB'J⟩
          | succ j =>
            have hj : j < k' := Nat.le_of_succ_le_succ hi
            obtain ⟨n', t', b', hle', hPush', hlt', hleJ'⟩ := hstep' j hj
            exact ⟨n', t', b', hle', hPush', hlt', hleJ'⟩
  obtain ⟨k, f, hf0, hfk, hsucc, hstep⟩ := H _ A (le_refl A) hAJ rfl
  refine ⟨k, fun i => f i.val, ?_, ?_, ?_, ?_⟩
  · exact hf0
  · exact hfk
  · intro i j hij
    have hmono : Monotone f := monotone_nat_of_le_succ hsucc
    exact hmono hij
  · intro i h
    obtain ⟨n, t, b, hle, hPush, hlt, hleJ⟩ := hstep i h
    exact ⟨n, t, b, hle, hPush, hlt, hleJ⟩

end boundary
end SSet
