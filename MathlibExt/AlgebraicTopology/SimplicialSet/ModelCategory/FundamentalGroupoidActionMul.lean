/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidAction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace

/-!
# Multiplicativity of the fundamental-groupoid action

The fundamental groupoid acts on every positive simplicial homotopy group by
multiplicative equivalences.  The proof fills an explicitly braided
path-space horn; tensor-factor swaps are never treated as definitional.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra Limits
open scoped SSet.modelCategoryQuillen Simplicial

namespace SSet.KanComplex.π

private noncomputable def actionPathSimplex
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y} {s : X.PtSimplex (m + 1) x}
    {t : X.PtSimplex (m + 1) y}
    (A : FundamentalGroupoid.ActionStruct e s t) :
    (Δ[m + 1] : SSet.{u}) ⟶ SSet.pathSpace X :=
  MonoidalClosed.curry
    ((β_ (Δ[1] : SSet.{u}) (Δ[m + 1] : SSet.{u})).hom ≫ A.prism)

private lemma actionPathSimplex_naturality
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y} {s : X.PtSimplex (m + 1) x}
    {t : X.PtSimplex (m + 1) y}
    (A : FundamentalGroupoid.ActionStruct e s t)
    {D : SSet.{u}} (θ : D ⟶ Δ[m + 1]) :
    θ ≫ actionPathSimplex A =
      MonoidalClosed.curry
        ((β_ (Δ[1] : SSet.{u}) D).hom ≫
          (θ ▷ (Δ[1] : SSet.{u})) ≫ A.prism) := by
  unfold actionPathSimplex
  rw [← MonoidalClosed.curry_natural_left]
  apply congrArg MonoidalClosed.curry
  rw [BraidedCategory.braiding_naturality_right_assoc]

private noncomputable def edgePathSimplex
    {X : SSet.{u}} {x y : X _⦋0⦌} (D : SSet.{u}) (e : X.Edge x y) :
    D ⟶ SSet.pathSpace X :=
  MonoidalClosed.curry
    (fst (Δ[1] : SSet.{u}) D ≫ SSet.yonedaEquiv.symm e.edge)

private lemma edgePathSimplex_naturality
    {X : SSet.{u}} {x y : X _⦋0⦌} {D D' : SSet.{u}}
    (θ : D' ⟶ D) (e : X.Edge x y) :
    θ ≫ edgePathSimplex D e = edgePathSimplex D' e := by
  unfold edgePathSimplex
  rw [← MonoidalClosed.curry_natural_left]
  apply congrArg MonoidalClosed.curry
  rw [← Category.assoc, whiskerLeft_fst]

private lemma edgePathSimplex_endpoints
    {X : SSet.{u}} {x y : X _⦋0⦌} (D : SSet.{u}) (e : X.Edge x y) :
    (edgePathSimplex D e ≫ (SSet.eval₀ : SSet.pathSpace X ⟶ X) = SSet.const x) ∧
      (edgePathSimplex D e ≫ (SSet.eval₁ : SSet.pathSpace X ⟶ X) = SSet.const y) := by
  constructor
  · rw [SSet.comp_eval₀_eq_ι₀_braiding_uncurry]
    unfold edgePathSimplex
    rw [MonoidalClosed.uncurry_curry]
    slice_lhs 2 3 => rw [braiding_hom_fst]
    rw [← Category.assoc, SSet.ι₀_snd, SSet.const_comp]
    congr 1
    have h_eq : stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ (1 : Fin 2)) := by
      have h := stdSimplex.δ_one_eq_const
      have hx := congrArg SSet.yonedaEquiv h
      simp [SSet.yonedaEquiv_const] at hx
      exact hx.symm
    rw [h_eq]
    change X.δ (1 : Fin 2) e.edge = x
    exact e.src_eq
  · rw [SSet.comp_eval₁_eq_ι₁_braiding_uncurry]
    unfold edgePathSimplex
    rw [MonoidalClosed.uncurry_curry]
    slice_lhs 2 3 => rw [braiding_hom_fst]
    rw [← Category.assoc, SSet.ι₁_snd, SSet.const_comp]
    congr 1
    have h_eq : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 2)) := by
      have h := stdSimplex.δ_zero_eq_const
      have hy := congrArg SSet.yonedaEquiv h
      simp [SSet.yonedaEquiv_const] at hy
      exact hy.symm
    rw [h_eq]
    change X.δ (0 : Fin 2) e.edge = y
    exact e.tgt_eq

private lemma actionPathSimplex_eval₀
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y} {s : X.PtSimplex (m + 1) x}
    {t : X.PtSimplex (m + 1) y}
    (A : FundamentalGroupoid.ActionStruct e s t) :
    actionPathSimplex A ≫ (SSet.eval₀ : SSet.pathSpace X ⟶ X) =
      SSet.RelativeMorphism.map s := by
  rw [SSet.comp_eval₀_eq_ι₀_braiding_uncurry]
  unfold actionPathSimplex
  rw [MonoidalClosed.uncurry_curry]
  slice_lhs 2 3 => rw [SymmetricCategory.symmetry]
  rw [Category.id_comp]
  exact A.left

private lemma actionPathSimplex_eval₁
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y} {s : X.PtSimplex (m + 1) x}
    {t : X.PtSimplex (m + 1) y}
    (A : FundamentalGroupoid.ActionStruct e s t) :
    actionPathSimplex A ≫ (SSet.eval₁ : SSet.pathSpace X ⟶ X) =
      SSet.RelativeMorphism.map t := by
  rw [SSet.comp_eval₁_eq_ι₁_braiding_uncurry]
  unfold actionPathSimplex
  rw [MonoidalClosed.uncurry_curry]
  slice_lhs 2 3 => rw [SymmetricCategory.symmetry]
  rw [Category.id_comp]
  exact A.right

private lemma actionPathSimplex_boundary
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y} {s : X.PtSimplex (m + 1) x}
    {t : X.PtSimplex (m + 1) y}
    (A : FundamentalGroupoid.ActionStruct e s t) :
    (SSet.boundary (m + 1)).ι ≫ actionPathSimplex A =
      edgePathSimplex (SSet.boundary (m + 1)) e := by
  rw [actionPathSimplex_naturality]
  unfold edgePathSimplex
  apply_fun MonoidalClosed.uncurry
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  rw [A.boundary]
  rw [← Category.assoc, braiding_hom_snd]

private noncomputable def actionMulFaces
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y}
    {s₁ s₂ : X.PtSimplex (m + 1) x}
    {t₁ t₂ : X.PtSimplex (m + 1) y}
    (A₁ : FundamentalGroupoid.ActionStruct e s₁ t₁)
    (A₂ : FundamentalGroupoid.ActionStruct e s₂ t₂)
    (j : Fin (m + 3))
    (_hj : j ≠ (Fin.last m).castSucc.succ) :
    (Δ[m + 1] : SSet.{u}) ⟶ SSet.pathSpace X :=
  if j = (Fin.last m).castSucc.castSucc then actionPathSimplex A₂
  else if j = (Fin.last m).succ.succ then actionPathSimplex A₁
  else edgePathSimplex (Δ[m + 1] : SSet.{u}) e

private lemma actionMulFaces_compatible
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y}
    {s₁ s₂ : X.PtSimplex (m + 1) x}
    {t₁ t₂ : X.PtSimplex (m + 1) y}
    (A₁ : FundamentalGroupoid.ActionStruct e s₁ t₁)
    (A₂ : FundamentalGroupoid.ActionStruct e s₂ t₂) :
    SSet.horn.IsCompatible (fun j hj ↦ actionMulFaces A₁ A₂ j hj) := by
  rw [SSet.horn.isCompatible_iff]
  intro j l hj hl hjl
  have haction₁ (r : Fin (m + 2)) :
      stdSimplex.δ r ≫ actionPathSimplex A₁ =
        edgePathSimplex (Δ[m] : SSet.{u}) e := by
    rw [← SSet.boundary.ι_ι_assoc, actionPathSimplex_boundary,
      edgePathSimplex_naturality]
  have haction₂ (r : Fin (m + 2)) :
      stdSimplex.δ r ≫ actionPathSimplex A₂ =
        edgePathSimplex (Δ[m] : SSet.{u}) e := by
    rw [← SSet.boundary.ι_ι_assoc, actionPathSimplex_boundary,
      edgePathSimplex_naturality]
  have hedge (r : Fin (m + 2)) :
      stdSimplex.δ r ≫ edgePathSimplex (Δ[m + 1] : SSet.{u}) e =
        edgePathSimplex (Δ[m] : SSet.{u}) e :=
    edgePathSimplex_naturality (stdSimplex.δ r) e
  have hface (a : Fin (m + 3))
      (ha : a ≠ (Fin.last m).castSucc.succ) (r : Fin (m + 2)) :
      stdSimplex.δ r ≫ actionMulFaces A₁ A₂ a ha =
        edgePathSimplex (Δ[m] : SSet.{u}) e := by
    unfold actionMulFaces
    split_ifs
    · exact haction₂ r
    · exact haction₁ r
    · exact hedge r
  rw [hface, hface]

private lemma actionMulFaces_eval₀
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y}
    {s₁ s₂ s₁₂ : X.PtSimplex (m + 1) x}
    {t₁ t₂ : X.PtSimplex (m + 1) y}
    (M : PtSimplex.MulStruct s₁ s₂ s₁₂ (Fin.last m))
    (A₁ : FundamentalGroupoid.ActionStruct e s₁ t₁)
    (A₂ : FundamentalGroupoid.ActionStruct e s₂ t₂)
    (j : Fin (m + 3)) (hj : j ≠ (Fin.last m).castSucc.succ) :
    actionMulFaces A₁ A₂ j hj ≫ (SSet.eval₀ : SSet.pathSpace X ⟶ X) =
      stdSimplex.δ j ≫ M.map := by
  unfold actionMulFaces
  split_ifs with h₂ h₁
  · subst j
    rw [actionPathSimplex_eval₀]
    exact M.δ_castSucc_castSucc_map.symm
  · subst j
    rw [actionPathSimplex_eval₀]
    exact M.δ_succ_succ_map.symm
  · rw [(edgePathSimplex_endpoints (Δ[m + 1] : SSet.{u}) e).1]
    symm
    apply M.δ_map_of_lt
    simp [Fin.ext_iff, Fin.lt_def] at h₂ h₁ hj ⊢
    omega

private theorem actionMulActionStruct
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    {e : X.Edge x y}
    {s₁ s₂ s₁₂ : X.PtSimplex (m + 1) x}
    {t₁ t₂ : X.PtSimplex (m + 1) y}
    (M : PtSimplex.MulStruct s₁ s₂ s₁₂ (Fin.last m))
    (A₁ : FundamentalGroupoid.ActionStruct e s₁ t₁)
    (A₂ : FundamentalGroupoid.ActionStruct e s₂ t₂) :
    ∃ t₁₂ : X.PtSimplex (m + 1) y,
      Nonempty (PtSimplex.MulStruct t₁ t₂ t₁₂ (Fin.last m)) ∧
        Nonempty (FundamentalGroupoid.ActionStruct e s₁₂ t₁₂) := by
  let hf := actionMulFaces_compatible A₁ A₂
  let comm := actionMulFaces_eval₀ M A₁ A₂
  let L : (Δ[m + 2] : SSet.{u}) ⟶ SSet.pathSpace X :=
    hf.lift SSet.eval₀ M.map comm
  have hLcomp : L ≫ (SSet.eval₀ : SSet.pathSpace X ⟶ X) = M.map :=
    hf.lift_comp SSet.eval₀ M.map comm
  have hLface (j : Fin (m + 3))
      (hj : j ≠ (Fin.last m).castSucc.succ) :
      stdSimplex.δ j ≫ L = actionMulFaces A₁ A₂ j hj :=
    hf.δ_lift SSet.eval₀ M.map comm j hj
  let k : Fin (m + 3) := (Fin.last m).castSucc.succ
  let j₂ : Fin (m + 3) := (Fin.last m).castSucc.castSucc
  let j₁ : Fin (m + 3) := (Fin.last m).succ.succ
  let q : (Δ[m + 1] : SSet.{u}) ⟶ SSet.pathSpace X := stdSimplex.δ k ≫ L
  have hL₂ : stdSimplex.δ j₂ ≫ L = actionPathSimplex A₂ := by
    have hne : j₂ ≠ (Fin.last m).castSucc.succ := by
      apply ne_of_lt
      simp [j₂, Fin.lt_def]
    rw [hLface j₂ hne]
    simp [actionMulFaces, j₂]
  have hL₁ : stdSimplex.δ j₁ ≫ L = actionPathSimplex A₁ := by
    have hne : j₁ ≠ (Fin.last m).castSucc.succ := by
      apply ne_of_gt
      simp [j₁, Fin.lt_def]
    have hne₂ : j₁ ≠ (Fin.last m).castSucc.castSucc := by
      apply ne_of_gt
      simp [j₁, Fin.lt_def]
    rw [hLface j₁ hne]
    unfold actionMulFaces
    split
    · rename_i h
      exact (hne₂ h).elim
    · split
      · rfl
      · rename_i h
        exact (h rfl).elim
  have hLconst (j : Fin (m + 3))
      (hj : j < (Fin.last m).castSucc.castSucc) :
      stdSimplex.δ j ≫ L = edgePathSimplex (Δ[m + 1] : SSet.{u}) e := by
    have hj₂k : (Fin.last m).castSucc.castSucc <
        (Fin.last m).castSucc.succ := by simp [Fin.lt_def]
    have hne : j ≠ (Fin.last m).castSucc.succ :=
      ne_of_lt (hj.trans hj₂k)
    rw [hLface j hne]
    unfold actionMulFaces
    split_ifs with h₂ h₁
    · subst j
      exact (lt_irrefl _ hj).elim
    · subst j
      have hj₂j₁ : (Fin.last m).castSucc.castSucc <
          (Fin.last m).succ.succ := by simp [Fin.lt_def]
      exact (not_lt_of_ge hj₂j₁.le hj).elim
    · rfl
  have hq_boundary :
      (SSet.boundary (m + 1)).ι ≫ q =
        edgePathSimplex (SSet.boundary (m + 1)) e := by
    apply SSet.boundary.hom_ext
    intro r
    rw [SSet.boundary.ι_ι_assoc]
    have hedgeBoundary :
        SSet.boundary.ι r ≫ edgePathSimplex (SSet.boundary (m + 1)) e =
          edgePathSimplex (Δ[m] : SSet.{u}) e :=
      edgePathSimplex_naturality (SSet.boundary.ι r) e
    change stdSimplex.δ r ≫ stdSimplex.δ k ≫ L = _
    by_cases hr : r.castSucc < k
    · let r' : Fin (m + 2) := k.pred (by simp [k])
      have hrle : r ≤ r' := by
        change r.val ≤ m
        change r.val < m + 1 at hr
        omega
      have hk : r'.succ = k := by
        apply Fin.ext
        simp [r', k]
      have hδ : stdSimplex.δ r ≫ stdSimplex.δ k =
          stdSimplex.δ r' ≫ stdSimplex.δ r.castSucc := by
        rw [← hk]
        exact stdSimplex.δ_comp_δ hrle
      rw [← Category.assoc, hδ, Category.assoc]
      rw [hLface r.castSucc (ne_of_lt hr)]
      have hface : stdSimplex.δ r' ≫
          actionMulFaces A₁ A₂ r.castSucc (ne_of_lt hr) =
            edgePathSimplex (Δ[m] : SSet.{u}) e := by
        unfold actionMulFaces
        split_ifs
        · rw [← SSet.boundary.ι_ι_assoc, actionPathSimplex_boundary,
            edgePathSimplex_naturality]
        · rw [← SSet.boundary.ι_ι_assoc, actionPathSimplex_boundary,
            edgePathSimplex_naturality]
        · exact edgePathSimplex_naturality (stdSimplex.δ r') e
      rw [hface, hedgeBoundary]
    · have hrval : r.val = m + 1 := by
        change ¬r.val < m + 1 at hr
        have := r.isLt
        omega
      have hr_eq : r.castSucc = k := by
        apply Fin.ext
        simp [k, hrval]
      have hr_succ : r.succ = j₁ := by
        apply Fin.ext
        simp [j₁, hrval]
      have hδ : stdSimplex.δ r ≫ stdSimplex.δ k =
          stdSimplex.δ r ≫ stdSimplex.δ j₁ := by
        rw [← hr_eq, ← hr_succ]
        exact stdSimplex.δ_comp_δ_self
      rw [← Category.assoc, hδ, Category.assoc, hL₁]
      rw [← SSet.boundary.ι_ι_assoc, actionPathSimplex_boundary]
  let t₁₂ : X.PtSimplex (m + 1) y :=
    { map := q ≫ SSet.eval₁
      comm := by
        simp only [Subcomplex.ofSimplex_ι, SSet.comp_const]
        rw [← Category.assoc, hq_boundary]
        exact (edgePathSimplex_endpoints (SSet.boundary (m + 1)) e).2 }
  let M₁ : (Δ[m + 2] : SSet.{u}) ⟶ X := L ≫ SSet.eval₁
  have htarget : PtSimplex.MulStruct t₁ t₂ t₁₂ (Fin.last m) :=
    { map := M₁
      δ_castSucc_castSucc_map := by
        dsimp only [M₁]
        rw [← Category.assoc, show (Fin.last m).castSucc.castSucc = j₂ from rfl,
          hL₂, actionPathSimplex_eval₁]
      δ_succ_castSucc_map := by
        dsimp only [M₁, t₁₂, q]
        rw [Category.assoc]
      δ_succ_succ_map := by
        dsimp only [M₁]
        rw [← Category.assoc, show (Fin.last m).succ.succ = j₁ from rfl,
          hL₁, actionPathSimplex_eval₁]
      δ_map_of_lt := by
        intro j hj
        dsimp only [M₁]
        rw [← Category.assoc, hLconst j hj]
        exact (edgePathSimplex_endpoints (Δ[m + 1] : SSet.{u}) e).2
      δ_map_of_gt := by
        intro j hj
        exact (not_lt_of_ge (Fin.le_last j) hj).elim }
  let omittedPrism : (Δ[m + 1] : SSet.{u}) ⊗ Δ[1] ⟶ X :=
    (β_ (Δ[m + 1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
      MonoidalClosed.uncurry q
  have homitted : FundamentalGroupoid.ActionStruct e s₁₂ t₁₂ :=
    { prism := omittedPrism
      left := by
        calc
          SSet.ι₀ ≫ omittedPrism =
              q ≫ (SSet.eval₀ : SSet.pathSpace X ⟶ X) :=
            (SSet.comp_eval₀_eq_ι₀_braiding_uncurry q).symm
          _ = stdSimplex.δ k ≫ (L ≫ SSet.eval₀) := by rfl
          _ = stdSimplex.δ k ≫ M.map := by rw [hLcomp]
          _ = SSet.RelativeMorphism.map s₁₂ := by
            exact M.δ_succ_castSucc_map
      right := by
        calc
          SSet.ι₁ ≫ omittedPrism =
              q ≫ (SSet.eval₁ : SSet.pathSpace X ⟶ X) :=
            (SSet.comp_eval₁_eq_ι₁_braiding_uncurry q).symm
          _ = SSet.RelativeMorphism.map t₁₂ := rfl
      boundary := by
        dsimp only [omittedPrism]
        rw [BraidedCategory.braiding_naturality_left_assoc]
        rw [← MonoidalClosed.uncurry_natural_left]
        rw [hq_boundary]
        unfold edgePathSimplex
        rw [MonoidalClosed.uncurry_curry]
        rw [← Category.assoc, braiding_hom_fst] }
  exact ⟨t₁₂, ⟨htarget⟩, ⟨homitted⟩⟩

/-- The fundamental-groupoid action preserves multiplication in every
positive simplicial homotopy group. -/
theorem action_mul
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (a b : π (m + 1) X x) :
    action p (a * b) = action p a * action p b := by
  induction p using FundamentalGroupoid.hom_rec_of_kanComplex with
  | homMk e =>
      induction a using π.rec with
      | mk s₁ =>
          induction b using π.rec with
          | mk s₂ =>
              obtain ⟨s₁₂, ⟨M⟩⟩ :=
                PtSimplex.MulStruct.nonempty s₁ s₂ (Fin.last m)
              obtain ⟨t₁, ⟨A₁⟩⟩ := FundamentalGroupoid.exists_actionStruct e s₁
              obtain ⟨t₂, ⟨A₂⟩⟩ := FundamentalGroupoid.exists_actionStruct e s₂
              obtain ⟨t₁₂, ⟨targetMul⟩, ⟨omittedAction⟩⟩ :=
                actionMulActionStruct M A₁ A₂
              rw [M.mul_eq]
              rw [action_homMk_mk_eq_mk_of_actionStruct omittedAction]
              rw [action_homMk_mk_eq_mk_of_actionStruct A₁]
              rw [action_homMk_mk_eq_mk_of_actionStruct A₂]
              exact targetMul.mul_eq.symm

/-- Multiplicative equivalence induced by a fundamental-groupoid morphism. -/
noncomputable def actionMulEquiv
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y) :
    π (m + 1) X x ≃* π (m + 1) X y :=
  { actionEquiv p with
    map_mul' := action_mul p }

@[simp]
theorem actionMulEquiv_apply
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y : X _⦋0⦌}
    (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (a : π (m + 1) X x) :
    actionMulEquiv p a = action p a :=
  rfl

@[simp]
theorem actionMulEquiv_id
    {X : SSet.{u}} [KanComplex X] {m : ℕ} (x : X _⦋0⦌) :
    actionMulEquiv (m := m) (𝟙 (FundamentalGroupoid.mk (X := X) x)) =
      MulEquiv.refl (π (m + 1) X x) := by
  ext a
  exact congrFun (action_id (X := X) (n := m + 1) x) a

/-- Multiplicative action equivalences compose in source-first order. -/
theorem actionMulEquiv_comp
    {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y z : X _⦋0⦌}
    (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (q : FundamentalGroupoid.mk (X := X) y ⟶ FundamentalGroupoid.mk z) :
    actionMulEquiv (m := m) (p ≫ q) =
      (actionMulEquiv (m := m) p).trans (actionMulEquiv (m := m) q) := by
  ext a
  exact congrFun (action_comp (n := m + 1) p q) a

end SSet.KanComplex.π
