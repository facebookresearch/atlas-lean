/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-! ## Equidecomposability calculus -/

/-- Two sets are congruent by finitely many isometries: there is a bijection from `A`
onto `B` that agrees pointwise with one of finitely many ambient isometries. -/
private def btCongr {X : Type*} [MetricSpace X] (A B : Set X) : Prop :=
  ∃ (f : X → X) (S : Set (X ≃ᵢ X)),
    S.Finite ∧ Set.BijOn f A B ∧ ∀ x ∈ A, ∃ g ∈ S, f x = g x

/-- btCongr is reflexive. -/
private theorem btCongr_refl {X : Type*} [MetricSpace X] (A : Set X) :
    btCongr A A := by
  refine ⟨id, {IsometryEquiv.refl X}, Set.finite_singleton _,
    ⟨fun x hx => hx, fun x _ y _ h => h, fun y hy => ⟨y, hy, rfl⟩⟩, ?_⟩
  intro x _
  exact ⟨IsometryEquiv.refl X, rfl, rfl⟩

/-- btCongr is symmetric. -/
private theorem btCongr_symm {X : Type*} [MetricSpace X] {A B : Set X}
    (h : btCongr A B) : btCongr B A := by
  obtain ⟨f, S, hfin, hbij, hloc⟩ := h
  by_cases hA : A.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hA
    have : Nonempty X := ⟨x₀⟩
    have hinv : Set.InvOn f (Function.invFunOn f A) B A :=
      ⟨(hbij.invOn_invFunOn).2, (hbij.invOn_invFunOn).1⟩
    have hbij' : Set.BijOn (Function.invFunOn f A) B A :=
      Set.BijOn.symm hinv hbij
    refine ⟨Function.invFunOn f A, S.image IsometryEquiv.symm, hfin.image _,
      hbij', ?_⟩
    intro y hyB
    have hxA : Function.invFunOn f A y ∈ A := hbij'.mapsTo hyB
    have hfy : f (Function.invFunOn f A y) = y := hinv.1 hyB
    obtain ⟨g, hgS, hgx⟩ := hloc _ hxA
    refine ⟨g.symm, ⟨g, hgS, rfl⟩, ?_⟩
    rw [hfy] at hgx
    have hgg : Function.invFunOn f A y =
        g.symm (g (Function.invFunOn f A y)) := by
      rw [IsometryEquiv.symm_apply_apply]
    rw [hgg, ← hgx]
  · have hB : B = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨y, hy⟩ := hne
      obtain ⟨x, hxA, -⟩ := hbij.2.2 hy
      exact hA ⟨x, hxA⟩
    have hA' : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst hB
    subst hA'
    exact btCongr_refl ∅

/-- btCongr is transitive. -/
private theorem btCongr_trans {X : Type*} [MetricSpace X] {A B C : Set X}
    (h1 : btCongr A B) (h2 : btCongr B C) : btCongr A C := by
  obtain ⟨f1, S1, hfin1, hbij1, hloc1⟩ := h1
  obtain ⟨f2, S2, hfin2, hbij2, hloc2⟩ := h2
  refine ⟨f2 ∘ f1, S1.image2 (fun g1 g2 => g1.trans g2) S2, hfin1.image2 _ hfin2,
    hbij2.comp hbij1, ?_⟩
  intro x hxA
  obtain ⟨g1, hg1, hg1x⟩ := hloc1 x hxA
  obtain ⟨g2, hg2, hg2x⟩ := hloc2 (f1 x) (hbij1.mapsTo hxA)
  refine ⟨g1.trans g2, Set.mem_image2_of_mem hg1 hg2, ?_⟩
  rw [Function.comp_apply, IsometryEquiv.trans_apply, hg1x]
  rw [hg1x] at hg2x
  exact hg2x

/-- btCongr is closed under disjoint unions. -/
private theorem btCongr_union {X : Type*} [MetricSpace X] {A₁ A₂ B₁ B₂ : Set X}
    (h1 : btCongr A₁ B₁) (h2 : btCongr A₂ B₂)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂) :
    btCongr (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  obtain ⟨f1, S1, hfin1, hbij1, hloc1⟩ := h1
  obtain ⟨f2, S2, hfin2, hbij2, hloc2⟩ := h2
  classical
  have hA2 : ∀ x ∈ A₂, x ∉ A₁ := fun x hx2 hx1 =>
    Set.disjoint_left.mp hdA hx1 hx2
  have e1 : ∀ x ∈ A₁, (fun x => if x ∈ A₁ then f1 x else f2 x) x = f1 x :=
    fun x hx => ite_eq_left hx
  have e2 : ∀ x ∈ A₂, (fun x => if x ∈ A₁ then f1 x else f2 x) x = f2 x :=
    fun x hx => ite_eq_right (hA2 x hx)
  have hB1 : Set.BijOn (fun x => if x ∈ A₁ then f1 x else f2 x) A₁ B₁ :=
    hbij1.congr (fun x hx => (e1 x hx).symm)
  have hB2 : Set.BijOn (fun x => if x ∈ A₁ then f1 x else f2 x) A₂ B₂ :=
    hbij2.congr (fun x hx => (e2 x hx).symm)
  have hinj : Set.InjOn (fun x => if x ∈ A₁ then f1 x else f2 x) (A₁ ∪ A₂) := by
    intro x hx y hy hxy
    rw [Set.mem_union] at hx hy
    by_cases hx1 : x ∈ A₁ <;> by_cases hy1 : y ∈ A₁
    · rw [e1 x hx1, e1 y hy1] at hxy
      exact hbij1.2.1 hx1 hy1 hxy
    · have hy2 : y ∈ A₂ := hy.resolve_left hy1
      rw [e1 x hx1, e2 y hy2] at hxy
      have h1 : f1 x ∈ B₁ := hbij1.mapsTo hx1
      have h2 : f1 x ∈ B₂ := hxy ▸ hbij2.mapsTo hy2
      exact False.elim (Set.disjoint_left.mp hdB h1 h2)
    · have hx2 : x ∈ A₂ := hx.resolve_left hx1
      rw [e2 x hx2, e1 y hy1] at hxy
      have h1 : f1 y ∈ B₁ := hbij1.mapsTo hy1
      have h2 : f1 y ∈ B₂ := hxy.symm ▸ hbij2.mapsTo hx2
      exact False.elim (Set.disjoint_left.mp hdB h1 h2)
    · have hx2 : x ∈ A₂ := hx.resolve_left hx1
      have hy2 : y ∈ A₂ := hy.resolve_left hy1
      rw [e2 x hx2, e2 y hy2] at hxy
      exact hbij2.2.1 hx2 hy2 hxy
  refine ⟨fun x => if x ∈ A₁ then f1 x else f2 x, S1 ∪ S2, hfin1.union hfin2,
    hB1.union hB2 hinj, ?_⟩
  intro x hx
  rw [Set.mem_union] at hx
  rcases hx with hx1 | hx2
  · obtain ⟨g, hgS, hgx⟩ := hloc1 x hx1
    exact ⟨g, Set.mem_union_left _ hgS, by rw [e1 x hx1]; exact hgx⟩
  · obtain ⟨g, hgS, hgx⟩ := hloc2 x hx2
    exact ⟨g, Set.mem_union_right _ hgS, by rw [e2 x hx2]; exact hgx⟩

/-- An isometry maps any set congruently onto its image. -/
private theorem btCongr_self_image {X : Type*} [MetricSpace X]
    (g : X ≃ᵢ X) (A : Set X) : btCongr A (g '' A) := by
  refine ⟨g, {g}, Set.finite_singleton _, g.injective.bijOn_image, ?_⟩
  intro x _
  exact ⟨g, rfl, rfl⟩

/-- The absorption trick: if the forward orbit of `C` under `σ` stays in `Y` and
never returns to `C`, then `Y` is congruent to `Y \ C`. -/
private theorem btCongr_absorb {X : Type*} [MetricSpace X]
    (σ : X ≃ᵢ X) {C Y : Set X}
    (hY : ∀ n : ℕ, (⇑σ)^[n] '' C ⊆ Y)
    (hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((⇑σ)^[n] '' C) C) :
    btCongr Y (Y \ C) := by
  classical
  set Ct : Set X := ⋃ n, (⇑σ)^[n] '' C with hCt
  have hCsub : C ⊆ Ct := by
    intro c hc
    rw [hCt]
    exact Set.mem_iUnion.mpr ⟨0, c, hc, rfl⟩
  have htsub : Ct ⊆ Y := Set.iUnion_subset hY
  have hiter : ∀ (n : ℕ) (c : X), (⇑σ)^[n.succ] c = σ ((⇑σ)^[n] c) :=
    fun n c => Function.iterate_succ_apply' _ n c
  have hmem : ∀ (n : ℕ) (c : X), c ∈ C → (⇑σ)^[n] c ∈ Ct := by
    intro n c hc
    rw [hCt]
    exact Set.mem_iUnion.mpr ⟨n, c, hc, rfl⟩
  have hsigCt : ∀ x ∈ Ct, σ x ∈ Ct := by
    intro x hx
    rw [hCt, Set.mem_iUnion] at hx
    obtain ⟨n, c, hcC, rfl⟩ := hx
    rw [← hiter n c]
    exact hmem n.succ c hcC
  have e1 : ∀ x ∈ Ct, (fun x => if x ∈ Ct then σ x else x) x = σ x :=
    fun x hx => ite_eq_left hx
  have e2 : ∀ x ∉ Ct, (fun x => if x ∈ Ct then σ x else x) x = x :=
    fun x hx => ite_eq_right hx
  refine ⟨fun x => if x ∈ Ct then σ x else x, {σ, IsometryEquiv.refl X},
    (Set.finite_singleton _).union (Set.finite_singleton _), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hxY
    by_cases hxCt : x ∈ Ct
    · rw [e1 x hxCt]
      refine ⟨htsub (hsigCt x hxCt), ?_⟩
      rw [hCt, Set.mem_iUnion] at hxCt
      obtain ⟨n, c, hcC, rfl⟩ := hxCt
      intro hcon
      have hmemC : (⇑σ)^[n.succ] c ∈ (⇑σ)^[n.succ] '' C := ⟨c, hcC, rfl⟩
      have hcon' : (⇑σ)^[n.succ] c ∈ C := by
        rw [hiter n c]
        exact hcon
      exact Set.disjoint_left.mp
        (hdisj n.succ (Nat.succ_le_succ (Nat.zero_le n))) hmemC hcon'
    · rw [e2 x hxCt]
      refine ⟨hxY, ?_⟩
      exact fun hcon => hxCt (hCsub hcon)
  · intro x hxX y hyY heq
    by_cases hxCt : x ∈ Ct <;> by_cases hyCt : y ∈ Ct
    · rw [e1 x hxCt, e1 y hyCt] at heq
      exact σ.injective heq
    · rw [e1 x hxCt, e2 y hyCt] at heq
      exact False.elim (hyCt (heq ▸ hsigCt x hxCt))
    · rw [e2 x hxCt, e1 y hyCt] at heq
      exact False.elim (hxCt (heq.symm ▸ hsigCt y hyCt))
    · rw [e2 x hxCt, e2 y hyCt] at heq
      exact heq
  · intro y hyY
    obtain ⟨hyY', hyC⟩ := hyY
    by_cases hyCt : y ∈ Ct
    · rw [hCt, Set.mem_iUnion] at hyCt
      obtain ⟨n, hn⟩ := hyCt
      obtain ⟨c, hcC, hyc⟩ := hn
      cases n with
      | zero =>
        have hcc : c = y := hyc
        exact False.elim (hyC (hcc ▸ hcC))
      | succ m =>
        refine ⟨(⇑σ)^[m] c, htsub (hmem m c hcC), ?_⟩
        rw [e1 _ (hmem m c hcC), ← hiter m c]
        exact hyc
    · exact ⟨y, hyY', by rw [e2 y hyCt]⟩
  · intro x hxY
    by_cases hxCt : x ∈ Ct
    · rw [hCt, Set.mem_iUnion] at hxCt
      obtain ⟨n, c, hcC, rfl⟩ := hxCt
      exact ⟨σ, by simp, e1 _ (hmem n c hcC)⟩
    · exact ⟨IsometryEquiv.refl X, by simp, by rw [e2 x hxCt]; rfl⟩

/-! ## Orthogonal action on `EuclideanSpace ℝ (Fin 3)` -/

/-- Abbreviation for the ambient space. -/
private abbrev btE := EuclideanSpace ℝ (Fin 3)

/-- Matrices to operators on the ambient space. -/
private noncomputable def btToCLM :
    Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] (btE →L[ℝ] btE) :=
  Matrix.toEuclideanCLM

/-- The ambient isometry equivalence of a 3x3 real unitary (orthogonal) matrix. -/
private noncomputable def btIsoOfUnitary (U : Matrix.unitaryGroup (Fin 3) ℝ) :
    btE ≃ᵢ btE :=
  (Unitary.linearIsometryEquiv
    ⟨btToCLM (U : Matrix (Fin 3) (Fin 3) ℝ),
      Unitary.map_mem btToCLM U.2⟩).toIsometryEquiv

/-- Applying the isometry is matrix-times-vector on coordinates. -/
private theorem btIsoOfUnitary_apply (U : Matrix.unitaryGroup (Fin 3) ℝ) (x : btE) :
    WithLp.ofLp (btIsoOfUnitary U x) =
      Matrix.mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (WithLp.ofLp x) := rfl

/-- The action is multiplicative. -/
private theorem btIsoOfUnitary_mul (U V : Matrix.unitaryGroup (Fin 3) ℝ) (x : btE) :
    btIsoOfUnitary (U * V) x = btIsoOfUnitary U (btIsoOfUnitary V x) := by
  apply WithLp.ofLp_injective
  simp only [btIsoOfUnitary_apply, Submonoid.coe_mul, Matrix.mulVec_mulVec]

/-- The action of the identity matrix is the identity. -/
private theorem btIsoOfUnitary_one (x : btE) :
    btIsoOfUnitary 1 x = x := by
  apply WithLp.ofLp_injective
  simp only [btIsoOfUnitary_apply, Submonoid.coe_one, Matrix.one_mulVec]

/-- The action fixes the origin and preserves norms. -/
private theorem btIsoOfUnitary_zero (U : Matrix.unitaryGroup (Fin 3) ℝ) :
    btIsoOfUnitary U 0 = 0 := by
  change (Unitary.linearIsometryEquiv
    ⟨btToCLM (U : Matrix (Fin 3) (Fin 3) ℝ),
      Unitary.map_mem btToCLM U.2⟩).toLinearIsometry 0 = 0
  exact LinearIsometry.map_zero _

private theorem btIsoOfUnitary_norm (U : Matrix.unitaryGroup (Fin 3) ℝ) (x : btE) :
    ‖btIsoOfUnitary U x‖ = ‖x‖ := by
  change ‖(Unitary.linearIsometryEquiv
    ⟨btToCLM (U : Matrix (Fin 3) (Fin 3) ℝ),
      Unitary.map_mem btToCLM U.2⟩) x‖ = ‖x‖
  exact LinearIsometryEquiv.norm_map _ x

/-- A 2D rotation block in the (0, 1)-plane is unitary when `c ^ 2 + s ^ 2 = 1`. -/
private theorem btRotBlock_mem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    !![c, -s, 0; s, c, 0; 0, 0, (1 : ℝ)] ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  have hT : Matrix.transpose !![c, -s, 0; s, c, 0; 0, 0, (1 : ℝ)]
      = !![c, s, 0; -s, c, 0; 0, 0, (1 : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e00 : c * c + -s * -s + 0 * 0 = (1 : ℝ) := by linear_combination h
  have e01 : c * s + -s * c + 0 * 0 = (0 : ℝ) := by ring
  have e02 : c * 0 + -s * 0 + 0 * 1 = (0 : ℝ) := by ring
  have e10 : s * c + c * -s + 0 * 0 = (0 : ℝ) := by ring
  have e11 : s * s + c * c + 0 * 0 = (1 : ℝ) := by linear_combination h
  have e12 : s * 0 + c * 0 + 0 * 1 = (0 : ℝ) := by ring
  have e20 : 0 * c + 0 * -s + 1 * 0 = (0 : ℝ) := by ring
  have e21 : 0 * s + 0 * c + 1 * 0 = (0 : ℝ) := by ring
  have e22 : 0 * 0 + 0 * 0 + 1 * 1 = (1 : ℝ) := by ring
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hT, Matrix.mul_fin_three,
    Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- A 2D rotation block in the (0, 2)-plane is unitary when `c ^ 2 + s ^ 2 = 1`. -/
private theorem btRotBlockY_mem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    !![c, 0, -s; 0, 1, 0; s, 0, (c : ℝ)] ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  have hT : Matrix.transpose !![c, 0, -s; 0, 1, 0; s, 0, (c : ℝ)]
      = !![c, 0, s; 0, 1, 0; -s, 0, (c : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e00 : c * c + 0 * 0 + -s * -s = (1 : ℝ) := by linear_combination h
  have e01 : c * 0 + 0 * 1 + -s * 0 = (0 : ℝ) := by ring
  have e02 : c * s + 0 * 0 + -s * c = (0 : ℝ) := by ring
  have e10 : 0 * c + 1 * 0 + 0 * -s = (0 : ℝ) := by ring
  have e11 : 0 * 0 + 1 * 1 + 0 * 0 = (1 : ℝ) := by ring
  have e12 : 0 * s + 1 * 0 + 0 * c = (0 : ℝ) := by ring
  have e20 : s * c + 0 * 0 + c * -s = (0 : ℝ) := by ring
  have e21 : s * 0 + 0 * 1 + c * 0 = (0 : ℝ) := by ring
  have e22 : s * s + 0 * 0 + c * c = (1 : ℝ) := by linear_combination h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hT, Matrix.mul_fin_three,
    Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- A 2D rotation block in the (1, 2)-plane is unitary when `c ^ 2 + s ^ 2 = 1`. -/
private theorem btRotBlockX_mem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    !![(1 : ℝ), 0, 0; 0, c, -s; 0, s, c] ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  have hT : Matrix.transpose !![(1 : ℝ), 0, 0; 0, c, -s; 0, s, c]
      = !![(1 : ℝ), 0, 0; 0, c, s; 0, -s, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e00 : 1 * 1 + 0 * 0 + 0 * 0 = (1 : ℝ) := by ring
  have e01 : 1 * 0 + 0 * c + 0 * -s = (0 : ℝ) := by ring
  have e02 : 1 * 0 + 0 * s + 0 * c = (0 : ℝ) := by ring
  have e10 : 0 * 1 + c * 0 + -s * 0 = (0 : ℝ) := by ring
  have e11 : 0 * 0 + c * c + -s * -s = (1 : ℝ) := by linear_combination h
  have e12 : 0 * 0 + c * s + -s * c = (0 : ℝ) := by ring
  have e20 : 0 * 1 + s * 0 + c * 0 = (0 : ℝ) := by ring
  have e21 : 0 * 0 + s * c + c * -s = (0 : ℝ) := by ring
  have e22 : 0 * 0 + s * s + c * c = (1 : ℝ) := by linear_combination h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hT, Matrix.mul_fin_three,
    Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- Rotation about the z-axis. -/
private noncomputable def btRotZ (θ : ℝ) : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, (1 : ℝ)],
    btRotBlock_mem (Real.cos θ) (Real.sin θ)
      (by linear_combination Real.cos_sq_add_sin_sq θ)⟩

/-- Rotation about the y-axis. -/
private noncomputable def btRotY (θ : ℝ) : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![Real.cos θ, 0, -Real.sin θ; 0, 1, 0; Real.sin θ, 0, (Real.cos θ : ℝ)],
    btRotBlockY_mem (Real.cos θ) (Real.sin θ)
      (by linear_combination Real.cos_sq_add_sin_sq θ)⟩

/-- Rotation matrices unfold to their explicit entries. -/
private theorem btRotZ_mat (θ : ℝ) :
    (btRotZ θ : Matrix (Fin 3) (Fin 3) ℝ) =
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, (1 : ℝ)] :=
  rfl

private theorem btRotY_mat (θ : ℝ) :
    (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) =
      !![Real.cos θ, 0, -Real.sin θ; 0, 1, 0; Real.sin θ, 0, (Real.cos θ : ℝ)] :=
  rfl

/-- Composition laws for the rotations. -/
private theorem btRotY_add (a b : ℝ) : btRotY (a + b) = btRotY a * btRotY b := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, btRotY_mat, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_add, Real.sin_add] <;> ring

private theorem btRotZ_add (a b : ℝ) : btRotZ (a + b) = btRotZ a * btRotZ b := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, btRotZ_mat, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_add, Real.sin_add] <;> ring

private theorem btRotY_zero : btRotY 0 = 1 := by
  apply Subtype.ext
  simp only [btRotY_mat, Submonoid.coe_one, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_zero, Real.sin_zero]

private theorem btRotZ_zero : btRotZ 0 = 1 := by
  apply Subtype.ext
  simp only [btRotZ_mat, Submonoid.coe_one, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_zero, Real.sin_zero]

/-- Iterates of the rotation isometries. -/
private theorem btRotY_iterate (t : ℝ) (n : ℕ) (x : btE) :
    (btIsoOfUnitary (btRotY t))^[n] x = btIsoOfUnitary (btRotY (n * t)) x := by
  induction n with
  | zero => simp [Function.iterate_zero_apply, btRotY_zero, btIsoOfUnitary_one]
  | succ n ih =>
    rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply', ih,
      ← btIsoOfUnitary_mul, ← btRotY_add]
    have hcast : ((n + 1 : ℕ) : ℝ) * t = t + (n : ℝ) * t := by push_cast; ring
    rw [hcast]

/-- A vector fixed by the y-rotation with `(u 0, u 2) ≠ (0, 0)` forces `cos θ = 1`. -/
private theorem btRotY_fix_cos (θ : ℝ) (u : Fin 3 → ℝ)
    (h : Matrix.mulVec (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) u = u)
    (hne : (u 0, u 2) ≠ (0, 0)) : Real.cos θ = 1 := by
  rw [btRotY_mat] at h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h2
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, zero_mul, add_zero,
    Matrix.cons_val, neg_mul] at h0 h2
  have hS : u 0 ^ 2 + u 2 ^ 2 ≠ 0 := by
    intro hz
    have e1 : u 0 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 2 ^ 2 := sq_nonneg _
      linarith
    have e2 : u 2 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 2 ^ 2 := sq_nonneg _
      linarith
    rw [sq_eq_zero_iff] at e1 e2
    exact hne (by rw [e1, e2])
  have hcomb : Real.cos θ * (u 0 ^ 2 + u 2 ^ 2) = u 0 ^ 2 + u 2 ^ 2 := by
    linear_combination u 0 * h0 + u 2 * h2
  have hcomb2 : Real.cos θ * (u 0 ^ 2 + u 2 ^ 2)
      = 1 * (u 0 ^ 2 + u 2 ^ 2) := by
    rw [hcomb, one_mul]
  exact mul_right_cancel₀ hS hcomb2

/-- A vector fixed by the z-rotation with `(u 0, u 1) ≠ (0, 0)` forces `cos θ = 1`. -/
private theorem btRotZ_fix_cos (θ : ℝ) (u : Fin 3 → ℝ)
    (h : Matrix.mulVec (btRotZ θ : Matrix (Fin 3) (Fin 3) ℝ) u = u)
    (hne : (u 0, u 1) ≠ (0, 0)) : Real.cos θ = 1 := by
  rw [btRotZ_mat] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, zero_mul, add_zero,
    Matrix.cons_val, neg_mul] at h0 h1
  have hS : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
    intro hz
    have e1 : u 0 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 1 ^ 2 := sq_nonneg _
      linarith
    have e2 : u 1 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 1 ^ 2 := sq_nonneg _
      linarith
    rw [sq_eq_zero_iff] at e1 e2
    exact hne (by rw [e1, e2])
  have hcomb : Real.cos θ * (u 0 ^ 2 + u 1 ^ 2) = u 0 ^ 2 + u 1 ^ 2 := by
    linear_combination u 0 * h0 + u 1 * h1
  have hcomb2 : Real.cos θ * (u 0 ^ 2 + u 1 ^ 2)
      = 1 * (u 0 ^ 2 + u 1 ^ 2) := by
    rw [hcomb, one_mul]
  exact mul_right_cancel₀ hS hcomb2

/-! ## Free group generators and the integer model -/

/-- First generator: z-rotation by `arccos (3 / 5)`. -/
private noncomputable def btGenA : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![(3 : ℝ) / 5, -(4 / 5), 0; 4 / 5, 3 / 5, 0; 0, 0, 1],
    btRotBlock_mem ((3 : ℝ) / 5) (4 / 5) (by norm_num)⟩

/-- Second generator: x-rotation by `arccos (3 / 5)`. -/
private noncomputable def btGenB : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![(1 : ℝ), 0, 0; 0, 3 / 5, -(4 / 5); 0, 4 / 5, 3 / 5],
    btRotBlockX_mem ((3 : ℝ) / 5) (4 / 5) (by norm_num)⟩

/-- Generator matrices unfold to explicit entries. -/
private theorem btGenA_mat :
    (btGenA : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(3 : ℝ) / 5, -(4 / 5), 0; 4 / 5, 3 / 5, 0; 0, 0, 1] :=
  rfl

private theorem btGenB_mat :
    (btGenB : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(1 : ℝ), 0, 0; 0, 3 / 5, -(4 / 5); 0, 4 / 5, 3 / 5] :=
  rfl

/-- The two generators as a function on `Fin 2`. -/
private noncomputable def btGenFun : Fin 2 → Matrix.unitaryGroup (Fin 3) ℝ :=
  ![btGenA, btGenB]

/-- The homomorphism from the free group of rank 2 to rotations. -/
private noncomputable def btRho : FreeGroup (Fin 2) →* Matrix.unitaryGroup (Fin 3) ℝ :=
  FreeGroup.lift btGenFun

/-- The action of a free group word as an ambient isometry. -/
private noncomputable def btAct (w : FreeGroup (Fin 2)) : btE ≃ᵢ btE :=
  btIsoOfUnitary (btRho w)

/-- Action composition and identity. -/
private theorem btAct_mul (w v : FreeGroup (Fin 2)) (x : btE) :
    btAct (w * v) x = btAct w (btAct v x) := by
  simp only [btAct, map_mul, btIsoOfUnitary_mul]

private theorem btAct_one (x : btE) : btAct 1 x = x := by
  simp only [btAct, map_one, btIsoOfUnitary_one]

/-- Five times the generator for a letter, on integer vectors. -/
private def btIntGen (s : Fin 2 × Bool) (v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  if s = (0, true) then ![3 * v 0 - 4 * v 1, 4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (0, false) then ![3 * v 0 + 4 * v 1, -4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (1, true) then ![5 * v 0, 3 * v 1 - 4 * v 2, 4 * v 1 + 3 * v 2]
  else ![5 * v 0, 3 * v 1 + 4 * v 2, -4 * v 1 + 3 * v 2]

/-- Right fold of `btIntGen` over a word, starting from `e_y = (0, 1, 0)`. -/
private def btIntWord (L : List (Fin 2 × Bool)) : Fin 3 → ℤ :=
  L.foldr btIntGen ![0, 1, 0]

/-- The mod-5 direction of the first letter. -/
private def btEll (s : Fin 2 × Bool) : Fin 3 → ZMod 5 :=
  if s = (0, true) then ![1, 3, 0]
  else if s = (0, false) then ![3, 1, 0]
  else if s = (1, true) then ![0, 1, 3]
  else ![0, 3, 1]

/-- The first generator preserves cross products. -/
private theorem btCross_genA (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (btGenA : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btGenA : Matrix (Fin 3) (Fin 3) ℝ) v) =
      Matrix.mulVec (btGenA : Matrix (Fin 3) (Fin 3) ℝ)
        (crossProduct u v) := by
  rw [btGenA_mat]
  ext i
  fin_cases i <;>
    simp only [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.head_fin_const] <;>
    ring

/-- The second generator preserves cross products. -/
private theorem btCross_genB (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (btGenB : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btGenB : Matrix (Fin 3) (Fin 3) ℝ) v) =
      Matrix.mulVec (btGenB : Matrix (Fin 3) (Fin 3) ℝ)
        (crossProduct u v) := by
  rw [btGenB_mat]
  ext i
  fin_cases i <;>
    simp only [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.head_fin_const] <;>
    ring

/-- The transpose of a cross-preserving orthogonal matrix preserves cross
products. -/
private theorem btCross_transpose (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.unitaryGroup (Fin 3) ℝ)
    (hcross : ∀ u v : Fin 3 → ℝ,
      crossProduct (Matrix.mulVec M u) (Matrix.mulVec M v) =
        Matrix.mulVec M (crossProduct u v)) (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (Matrix.transpose M) u)
        (Matrix.mulVec (Matrix.transpose M) v) =
      Matrix.mulVec (Matrix.transpose M) (crossProduct u v) := by
  have hMtM : Matrix.transpose M * M = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hM
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hMMt : M * Matrix.transpose M = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hM
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hinj : Function.Injective (Matrix.mulVec M) := by
    intro a b hab
    have h2 := congrArg (Matrix.mulVec (Matrix.transpose M)) hab
    simp only [Matrix.mulVec_mulVec, hMtM, Matrix.one_mulVec] at h2
    exact h2
  have e : ∀ w : Fin 3 → ℝ,
      Matrix.mulVec M (Matrix.mulVec (Matrix.transpose M) w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hMMt, Matrix.one_mulVec]
  apply hinj
  simp only [← hcross, e]

/-- Every matrix in the image preserves cross products. -/
private theorem btRho_cross (w : FreeGroup (Fin 2)) (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) v) =
      Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) (crossProduct u v) := by
  induction w using FreeGroup.induction_on generalizing u v with
  | one =>
    simp only [map_one, Submonoid.coe_one, Matrix.one_mulVec]
  | of x =>
    have hx : x = 0 ∨ x = 1 := by fin_cases x <;> simp
    rcases hx with rfl | rfl
    · have h0 : (btRho (FreeGroup.of (0 : Fin 2)) : Matrix (Fin 3) (Fin 3) ℝ)
          = (btGenA : Matrix (Fin 3) (Fin 3) ℝ) := by
        simp only [btRho, FreeGroup.lift_apply_of, btGenFun,
          Matrix.cons_val_zero]
      rw [h0]
      exact btCross_genA u v
    · have h1 : (btRho (FreeGroup.of (1 : Fin 2)) : Matrix (Fin 3) (Fin 3) ℝ)
          = (btGenB : Matrix (Fin 3) (Fin 3) ℝ) := by
        simp only [btRho, FreeGroup.lift_apply_of, btGenFun,
          Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h1]
      exact btCross_genB u v
  | inv_of x ih =>
    have hM : (btRho ((FreeGroup.of x)⁻¹) : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.transpose (btRho (FreeGroup.of x) : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
        Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hM]
    exact btCross_transpose _ (btRho (FreeGroup.of x)).2 ih u v
  | mul x y ihx ihy =>
    have hM : (btRho (x * y) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btRho x : Matrix (Fin 3) (Fin 3) ℝ)
          * (btRho y : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [map_mul, Submonoid.coe_mul]
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ihx, ihy,
      Matrix.mulVec_mulVec]

/-- Every matrix in the image is orthogonal. -/
private theorem btRho_star_mul (w : FreeGroup (Fin 2)) :
    star (btRho w : Matrix (Fin 3) (Fin 3) ℝ) * (btRho w : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
  (Matrix.mem_unitaryGroup_iff').mp (btRho w).2

/-- Every matrix in the image preserves dot products. -/
private theorem btRho_dot (w : FreeGroup (Fin 2)) (u v : Fin 3 → ℝ) :
    dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) v) =
      dotProduct u v := by
  have hort : Matrix.transpose (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
      * (btRho w : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    have h := btRho_star_mul w
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hort, Matrix.vecMul_one]

/-- Transposes of the generators in explicit form. -/
private theorem btGenA_transpose :
    Matrix.transpose (btGenA : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(3 : ℝ) / 5, 4 / 5, 0; -(4 / 5), 3 / 5, 0; 0, 0, 1] := by
  rw [btGenA_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem btGenB_transpose :
    Matrix.transpose (btGenB : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(1 : ℝ), 0, 0; 0, 3 / 5, 4 / 5; 0, -(4 / 5), 3 / 5] := by
  rw [btGenB_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Five times a generator acts integrally on integer vectors. -/
private theorem btFiveGenA (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • (btGenA : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (0, true) v) i : ℤ) : ℝ) := by
  rw [btGenA_mat]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

private theorem btFiveGenAinv (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • Matrix.transpose (btGenA : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (0, false) v) i : ℤ) : ℝ) := by
  rw [btGenA_transpose]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

private theorem btFiveGenB (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • (btGenB : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (1, true) v) i : ℤ) : ℝ) := by
  rw [btGenB_mat]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

private theorem btFiveGenBinv (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • Matrix.transpose (btGenB : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (1, false) v) i : ℤ) : ℝ) := by
  rw [btGenB_transpose]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

/-- Single-letter step of the integer model. -/
private theorem btFiveGen_single (s : Fin 2 × Bool) (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • (btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen s v) i : ℤ) : ℝ) := by
  obtain ⟨x, b⟩ := s
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> simp
  rcases hx with rfl | rfl <;> cases b
  · have h1 : FreeGroup.mk [((0 : Fin 2), false)] = (FreeGroup.of (0 : Fin 2))⁻¹ := by
      have ho : FreeGroup.of (0 : Fin 2) = FreeGroup.mk [((0 : Fin 2), true)] := rfl
      rw [ho, FreeGroup.inv_mk]
      rfl
    have h0 : btRho (FreeGroup.of (0 : Fin 2)) = btGenA := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((0 : Fin 2), false)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.transpose (btGenA : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
        Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, h0]
    rw [hA]
    exact btFiveGenAinv v
  · have h1 : FreeGroup.mk [((0 : Fin 2), true)] = FreeGroup.of (0 : Fin 2) := rfl
    have h0 : btRho (FreeGroup.of (0 : Fin 2)) = btGenA := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((0 : Fin 2), true)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btGenA : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, h0]
    rw [hA]
    exact btFiveGenA v
  · have h1 : FreeGroup.mk [((1 : Fin 2), false)] = (FreeGroup.of (1 : Fin 2))⁻¹ := by
      have ho : FreeGroup.of (1 : Fin 2) = FreeGroup.mk [((1 : Fin 2), true)] := rfl
      rw [ho, FreeGroup.inv_mk]
      rfl
    have h0 : btRho (FreeGroup.of (1 : Fin 2)) = btGenB := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((1 : Fin 2), false)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.transpose (btGenB : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
        Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, h0]
    rw [hA]
    exact btFiveGenBinv v
  · have h1 : FreeGroup.mk [((1 : Fin 2), true)] = FreeGroup.of (1 : Fin 2) := rfl
    have h0 : btRho (FreeGroup.of (1 : Fin 2)) = btGenB := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((1 : Fin 2), true)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btGenB : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, h0]
    rw [hA]
    exact btFiveGenB v

/-- The integer model computes `5 ^ |L| • M_L e_y`. -/
private theorem btIntWord_spec (L : List (Fin 2 × Bool)) :
    (5 ^ L.length : ℝ) •
        (Matrix.mulVec (btRho (FreeGroup.mk L) : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, 0]) =
    fun i => ((btIntWord L i : ℤ) : ℝ) := by
  induction L with
  | nil =>
    have h1 : btRho (FreeGroup.mk []) = 1 := by
      simp only [btRho, FreeGroup.lift_mk, List.map_nil, List.prod_nil]
    simp only [List.length_nil, pow_zero, one_smul, h1, Submonoid.coe_one,
      Matrix.one_mulVec, btIntWord, List.foldr_nil]
    ext i
    fin_cases i <;> simp
  | cons s L' ih =>
    have hmk : FreeGroup.mk [s] * FreeGroup.mk L' = FreeGroup.mk (s :: L') :=
      FreeGroup.mul_mk
    have hM : (btRho (FreeGroup.mk (s :: L')) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ)
          * (btRho (FreeGroup.mk L') : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [← hmk, map_mul, Submonoid.coe_mul]
    have hscale : (5 : ℝ) ^ (L'.length + 1)
          • (Matrix.mulVec (((btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ)
            * (btRho (FreeGroup.mk L') : Matrix (Fin 3) (Fin 3) ℝ)))
            ![0, 1, (0 : ℝ)]) =
        Matrix.mulVec ((5 : ℝ) • (btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ))
          ((5 : ℝ) ^ L'.length
            • Matrix.mulVec (btRho (FreeGroup.mk L') : Matrix (Fin 3) (Fin 3) ℝ)
              ![0, 1, (0 : ℝ)]) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, ← mul_smul, ← pow_succ',
        Matrix.mulVec_mulVec]
    rw [hM, List.length_cons, hscale, ih, btFiveGen_single]
    simp only [btIntWord, List.foldr_cons]

/-- Mod-5 version of `btIntGen`, with the same coefficients. -/
private def btIntGenMod (s : Fin 2 × Bool) (v : Fin 3 → ZMod 5) : Fin 3 → ZMod 5 :=
  if s = (0, true) then ![3 * v 0 - 4 * v 1, 4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (0, false) then ![3 * v 0 + 4 * v 1, -4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (1, true) then ![5 * v 0, 3 * v 1 - 4 * v 2, 4 * v 1 + 3 * v 2]
  else ![5 * v 0, 3 * v 1 + 4 * v 2, -4 * v 1 + 3 * v 2]

/-- Casting commutes with the integer generator step. -/
private theorem btIntGen_cast (s : Fin 2 × Bool) (v : Fin 3 → ℤ) :
    (fun i => ((btIntGen s v i : ℤ) : ZMod 5)) =
      btIntGenMod s (fun i => ((v i : ℤ) : ZMod 5)) := by
  obtain ⟨x, b⟩ := s
  fin_cases x <;> cases b <;>
    ext i <;> fin_cases i <;>
    simp [btIntGen, btIntGenMod]

/-- Base case: the generator applied to `e_y` is a nonzero multiple of the
letter direction. -/
private theorem btIntWord_base :
    ∀ s : Fin 2 × Bool, ∃ c : ZMod 5, c ≠ 0 ∧
      (fun i => ((btIntGen s ![0, 1, 0] i : ℤ) : ZMod 5)) = c • btEll s := by
  decide

/-- Step case: applying a generator to a nonzero multiple of a non-inverse
letter direction stays a nonzero multiple of the new direction. -/
private theorem btIntWord_step :
    ∀ (s t : Fin 2 × Bool) (c : ZMod 5), (t.1 ≠ s.1 ∨ t.2 = s.2) → c ≠ 0 →
      ∃ c' : ZMod 5, c' ≠ 0 ∧
        btIntGenMod s (c • btEll t) = c' • btEll s := by
  decide

/-- The mod-5 reduction of a reduced word is a nonzero multiple of the first
letter's direction. -/
private theorem btIntWord_mod_five (s : Fin 2 × Bool) (L : List (Fin 2 × Bool))
    (h : FreeGroup.IsReduced (s :: L)) :
    ∃ c : ZMod 5, c ≠ 0 ∧
      (fun i => ((btIntWord (s :: L) i : ℤ) : ZMod 5)) = c • btEll s := by
  have aux : ∀ (L : List (Fin 2 × Bool)) (s : Fin 2 × Bool),
      FreeGroup.IsReduced (s :: L) →
      ∃ c : ZMod 5, c ≠ 0 ∧
        (fun i => ((btIntWord (s :: L) i : ℤ) : ZMod 5)) = c • btEll s := by
    intro L
    induction L with
    | nil =>
      intro s _
      have hfold : btIntWord [s] = btIntGen s ![0, 1, 0] := rfl
      rw [hfold]
      exact btIntWord_base s
    | cons t L' ih =>
      intro s hs
      have hcons := (FreeGroup.isReduced_cons_cons).mp hs
      have hside : t.1 ≠ s.1 ∨ t.2 = s.2 := by
        by_cases he : t.1 = s.1
        · right
          exact (hcons.1 he.symm).symm
        · left
          exact he
      obtain ⟨c, hcne, hc⟩ := ih t hcons.2
      obtain ⟨c', hc'ne, hc'⟩ := btIntWord_step s t c hside hcne
      refine ⟨c', hc'ne, ?_⟩
      have hfold : btIntWord (s :: t :: L') = btIntGen s (btIntWord (t :: L')) := rfl
      rw [hfold, btIntGen_cast, hc]
      exact hc'
  exact aux L s h

/-- The real `e_y` agrees with the cast of the integer `e_y`, coordinatewise. -/
private theorem btEy_cast (i : Fin 3) :
    ((![0, 1, (0 : ℤ)] i : ℤ) : ℝ) = ![0, 1, (0 : ℝ)] i := by
  fin_cases i <;> simp

/-- No nontrivial word fixes a nonzero multiple of `e_y`. -/
private theorem btRho_ey_ne (w : FreeGroup (Fin 2)) (hw : w ≠ 1)
    (s : ℝ) (hs : s ≠ 0) :
    ¬ Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) (s • ![0, 1, (0 : ℝ)]) =
      s • ![0, 1, (0 : ℝ)] := by
  intro hfix
  have h1 : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, (0 : ℝ)] =
      ![0, 1, (0 : ℝ)] := by
    have h2 : s • Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, (0 : ℝ)] =
        s • ![0, 1, (0 : ℝ)] := by
      rw [← Matrix.mulVec_smul]
      exact hfix
    ext i
    have hi := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hs hi
  have hne : w.toWord ≠ [] :=
    fun hempty => hw (FreeGroup.toWord_eq_nil_iff.mp hempty)
  cases hL : w.toWord with
  | nil => exact absurd hL hne
  | cons s0 L' =>
    have hred : FreeGroup.IsReduced (s0 :: L') := by
      rw [← hL]
      exact FreeGroup.isReduced_toWord
    have hmk : FreeGroup.mk (s0 :: L') = w := by
      rw [← hL]
      exact FreeGroup.mk_toWord
    have hspec := btIntWord_spec (s0 :: L')
    rw [hmk, h1] at hspec
    have hcast : ∀ i : Fin 3,
        ((5 * (5 ^ L'.length * ![0, 1, (0 : ℤ)] i) : ℤ) : ℝ) =
        (5 ^ (s0 :: L').length : ℝ) * ![0, 1, (0 : ℝ)] i := by
      intro i
      push_cast
      rw [btEy_cast i, List.length_cons, pow_succ]
      ring
    have hint : ∀ i, btIntWord (s0 :: L') i =
        5 * (5 ^ L'.length * ![0, 1, (0 : ℤ)] i) := by
      intro i
      have hi := congrFun hspec i
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      rw [← hcast i] at hi
      exact (Int.cast_injective hi).symm
    have hzero : (fun i => ((btIntWord (s0 :: L') i : ℤ) : ZMod 5)) = 0 := by
      ext i
      simp only [hint i, Pi.zero_apply]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_mul_right 5 _
    obtain ⟨c, hcne, hc⟩ := btIntWord_mod_five s0 L' hred
    rw [hzero] at hc
    have hell : ∀ t : Fin 2 × Bool, ∀ d : ZMod 5, d • btEll t = 0 → d = 0 := by
      decide
    exact hcne (hell s0 c hc.symm)

/-- A nontrivial word fixing `u` and `v` forces `u ⨯₃ v = 0`. -/
private theorem btFix_cross_eq_zero (w : FreeGroup (Fin 2)) (hw : w ≠ 1)
    (u v : Fin 3 → ℝ)
    (hu : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) u = u)
    (hv : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) v = v) :
    crossProduct u v = 0 := by
  by_contra hne
  have hnn : dotProduct (crossProduct u v) (crossProduct u v) ≠ 0 :=
    fun h0 => hne ((dotProduct_self_eq_zero).mp h0)
  have hMn : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
      (crossProduct u v) = crossProduct u v := by
    rw [← btRho_cross, hu, hv]
  have hdu : ∀ x : Fin 3 → ℝ,
      dotProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) u
        = 0 := by
    intro x
    have hMx : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x) u =
        dotProduct x u := by
      have e := btRho_dot w x u
      rw [hu] at e
      exact e
    rw [sub_dotProduct, hMx, sub_self]
  have hdv : ∀ x : Fin 3 → ℝ,
      dotProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) v
        = 0 := by
    intro x
    have hMx : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x) v =
        dotProduct x v := by
      have e := btRho_dot w x v
      rw [hv] at e
      exact e
    rw [sub_dotProduct, hMx, sub_self]
  have hdn : ∀ x : Fin 3 → ℝ,
      dotProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
        (crossProduct u v) = 0 := by
    intro x
    have hMx : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x)
        (crossProduct u v) =
        dotProduct x (crossProduct u v) := by
      have e := btRho_dot w x (crossProduct u v)
      rw [hMn] at e
      exact e
    rw [sub_dotProduct, hMx, sub_self]
  have hcross : ∀ x : Fin 3 → ℝ,
      crossProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
        (crossProduct u v) = 0 := by
    intro x
    have e := cross_cross_eq_smul_sub_smul'
      (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) u v
    have e2 : dotProduct u
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) = 0 := by
      rw [dotProduct_comm u, hdu x]
    rw [e, hdv x, e2]
    simp
  have hall : ∀ x : Fin 3 → ℝ,
      Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x = x := by
    intro x
    have e := cross_dot_cross
      (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
      (crossProduct u v)
      (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
      (crossProduct u v)
    rw [hcross x] at e
    simp only [zero_dotProduct] at e
    rw [hdn x] at e
    simp only [zero_mul, sub_zero] at e
    have eyy : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) = 0 :=
      (mul_eq_zero.mp e.symm).resolve_right hnn
    rw [dotProduct_self_eq_zero] at eyy
    exact sub_eq_zero.mp eyy
  have hey := hall ![0, 1, (0 : ℝ)]
  exact btRho_ey_ne w hw 1 one_ne_zero (by simpa using hey)

/-- Fixed vectors of a nontrivial word lie on one line through a unit vector
with `(u 0, u 2) ≠ (0, 0)`. -/
private theorem btAxis (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    ∃ u : Fin 3 → ℝ, dotProduct u u = 1 ∧ (u 0, u 2) ≠ (0, 0) ∧
      ∀ x : btE, btAct w x = x → ∃ s : ℝ, WithLp.ofLp x = s • u := by
  by_cases hfix : ∃ p : Fin 3 → ℝ, p ≠ 0 ∧
      Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) p = p
  · obtain ⟨p, hpne, hpp⟩ := hfix
    have hne : dotProduct p p ≠ 0 :=
      fun h0 => hpne ((dotProduct_self_eq_zero).mp h0)
    have hnn : 0 ≤ dotProduct p p := by
      change (0 : ℝ) ≤ ∑ i, p i * p i
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (p i))
    have hpos : 0 < dotProduct p p := lt_of_le_of_ne hnn (Ne.symm hne)
    have hrne : Real.sqrt (dotProduct p p) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hrsq : Real.sqrt (dotProduct p p) * Real.sqrt (dotProduct p p) =
        dotProduct p p :=
      Real.mul_self_sqrt (le_of_lt hpos)
    have key : ∀ (r X : ℝ), r ≠ 0 → r * r = X →
        (1 / r) * ((1 / r) * X) = 1 := by
      intro r X hr hrr
      rw [← hrr, one_div, ← mul_assoc, ← mul_inv]
      exact inv_mul_cancel₀ (mul_ne_zero hr hr)
    have huu : dotProduct ((1 / Real.sqrt (dotProduct p p)) • p)
        ((1 / Real.sqrt (dotProduct p p)) • p) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      exact key _ _ hrne hrsq
    have hnsub : (((1 / Real.sqrt (dotProduct p p)) • p) 0,
        ((1 / Real.sqrt (dotProduct p p)) • p) 2) ≠ (0, 0) := by
      intro hcon
      have hcon0 := congrArg Prod.fst hcon
      have hcon2 := congrArg Prod.snd hcon
      simp only [Pi.smul_apply, smul_eq_mul] at hcon0 hcon2
      have h0 : p 0 = 0 :=
        (mul_eq_zero.mp hcon0).resolve_left (div_ne_zero one_ne_zero hrne)
      have h2 : p 2 = 0 :=
        (mul_eq_zero.mp hcon2).resolve_left (div_ne_zero one_ne_zero hrne)
      have hp1 : p 1 ≠ 0 := by
        intro hz
        apply hpne
        ext i
        fin_cases i
        · simpa using h0
        · simpa using hz
        · simpa using h2
      have hpe : p = (p 1) • ![0, 1, (0 : ℝ)] := by
        ext i
        fin_cases i
        · simp [h0, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
        · simp [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
            Matrix.cons_val_zero]
        · simp [h2, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two,
            Matrix.tail_cons, Matrix.head_cons]
      have hfix1 : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
          ((p 1) • ![0, 1, (0 : ℝ)]) = (p 1) • ![0, 1, (0 : ℝ)] := by
        rw [← hpe]
        exact hpp
      exact btRho_ey_ne w hw (p 1) hp1 hfix1
    refine ⟨(1 / Real.sqrt (dotProduct p p)) • p, huu, hnsub, ?_⟩
    intro x hx
    have hMx : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
        (WithLp.ofLp x) = WithLp.ofLp x :=
      congrArg WithLp.ofLp hx
    have hMu : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
        ((1 / Real.sqrt (dotProduct p p)) • p) =
        (1 / Real.sqrt (dotProduct p p)) • p := by
      rw [Matrix.mulVec_smul, hpp]
    have hcr := btFix_cross_eq_zero w hw _ _ hMx hMu
    have hz : crossProduct ((1 / Real.sqrt (dotProduct p p)) • p) 0 = 0 := by
      simp
    have e := cross_cross_eq_smul_sub_smul'
      ((1 / Real.sqrt (dotProduct p p)) • p) (WithLp.ofLp x)
      ((1 / Real.sqrt (dotProduct p p)) • p)
    rw [hcr, hz, huu, one_smul] at e
    exact ⟨dotProduct (WithLp.ofLp x)
      ((1 / Real.sqrt (dotProduct p p)) • p), sub_eq_zero.mp e.symm⟩
  · refine ⟨![1, 0, (0 : ℝ)], ?_, ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
    · have e0 : (![1, 0, (0 : ℝ)] : Fin 3 → ℝ) 0 = 1 := by
        simp [Matrix.cons_val_zero]
      have e2 : (![1, 0, (0 : ℝ)] : Fin 3 → ℝ) 2 = 0 := by
        simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [e0, e2]
      simp
    · intro x hx
      have hMx : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
          (WithLp.ofLp x) = WithLp.ofLp x :=
        congrArg WithLp.ofLp hx
      refine ⟨0, ?_⟩
      simp only [zero_smul]
      by_contra hcon
      exact hfix ⟨WithLp.ofLp x, hcon, hMx⟩

/-- Choice of axis for each nontrivial word. -/
private noncomputable def btU (w : FreeGroup (Fin 2)) : Fin 3 → ℝ :=
  if h : w = 1 then ![1, 0, 0] else Classical.choose (btAxis w h)

/-- Unfolding the axis choice at a nontrivial word. -/
private theorem btU_eq (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    btU w = Classical.choose (btAxis w hw) := by
  simp only [btU, dite_eq_right hw]

/-- The chosen axis is a unit vector. -/
private theorem btU_dot (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    dotProduct (btU w) (btU w) = 1 := by
  rw [btU_eq w hw]
  exact (Classical.choose_spec (btAxis w hw)).1

/-- The chosen axis has `(u 0, u 2) ≠ (0, 0)`. -/
private theorem btU_nz (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    (btU w 0, btU w 2) ≠ (0, 0) := by
  rw [btU_eq w hw]
  exact (Classical.choose_spec (btAxis w hw)).2.1

/-- Fixed points of `btAct w` lie on the chosen axis. -/
private theorem btU_fix (w : FreeGroup (Fin 2)) (hw : w ≠ 1)
    (x : btE) (hx : btAct w x = x) :
    ∃ s : ℝ, WithLp.ofLp x = s • btU w := by
  rw [btU_eq w hw]
  exact (Classical.choose_spec (btAxis w hw)).2.2 x hx

/-! ## Bad set, free locus, and the paradoxical pieces of `F₂` -/

/-- Points fixed by some nontrivial word. -/
private def btBad : Set btE :=
  {z | z ≠ 0 ∧ ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ btAct w z = z}

/-- The free locus: the unit ball minus the centre and the bad axes. -/
private def btOmega : Set btE :=
  Metric.closedBall (0 : btE) 1 \ ({0} ∪ btBad)

/-- Words whose reduced form starts with a given letter. -/
private def btW (s : Fin 2 × Bool) : Set (FreeGroup (Fin 2)) :=
  {w | w.toWord.head? = some s}

/-- Nonpositive powers of the inverse of the first generator. -/
private def btT : Set (FreeGroup (Fin 2)) :=
  Set.range (fun n : ℕ => (FreeGroup.of (0 : Fin 2))⁻¹ ^ n)

/-- The four paradoxical pieces of the free group. -/
private def btP₁ : Set (FreeGroup (Fin 2)) := btW (0, true) ∪ btT

private def btP₂ : Set (FreeGroup (Fin 2)) := btW (0, false) \ btT

private def btP₃ : Set (FreeGroup (Fin 2)) := btW (1, true)

private def btP₄ : Set (FreeGroup (Fin 2)) := btW (1, false)

/-- The inverse generator is the one-letter word with flipped bit. -/
private theorem btInv_of (x : Fin 2) :
    (FreeGroup.of x)⁻¹ = FreeGroup.mk [(x, false)] := rfl

/-- The `toWord` of a nonpositive power of the inverse generator. -/
private theorem btT_word (n : ℕ) :
    ((FreeGroup.of (0 : Fin 2))⁻¹ ^ n).toWord =
      List.replicate n ((0 : Fin 2), false) := by
  rw [inv_pow, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow]
  simp [FreeGroup.invRev]

/-- The `toWord` of a generator is its single letter. -/
private theorem btToWord_of (x : Fin 2) :
    (FreeGroup.of x).toWord = [(x, true)] := by
  have h1 : FreeGroup.of x = FreeGroup.mk [(x, true)] := rfl
  rw [h1, FreeGroup.toWord_mk]
  exact FreeGroup.IsReduced.reduce_eq FreeGroup.IsReduced.singleton

/-- A generator lies in the piece for its own head letter. -/
private theorem btW_of (x : Fin 2) : FreeGroup.of x ∈ btW (x, true) := by
  change (FreeGroup.of x).toWord.head? = some (x, true)
  rw [btToWord_of x, List.head?_cons]

/-- Pieces for distinct head letters are disjoint. -/
private theorem btW_disjoint {s t : Fin 2 × Bool} (h : s ≠ t) :
    Disjoint (btW s) (btW t) := by
  rw [Set.disjoint_left]
  intro w hws hwt
  exact h (Option.some_inj.mp (hws.symm.trans hwt))

/-- The tail piece avoids every head letter except its own. -/
private theorem btT_disjoint_W {s : Fin 2 × Bool} (hs : s ≠ (0, false)) :
    Disjoint btT (btW s) := by
  rw [Set.disjoint_left]
  intro w hwT hw
  obtain ⟨n, rfl⟩ := hwT
  simp only [btW, Set.mem_ofPred_eq] at hw
  rw [btT_word] at hw
  cases n with
  | zero =>
    rw [List.replicate_zero] at hw
    have hsn : (some s : Option (Fin 2 × Bool)) = none := hw.symm
    exact Option.some_ne_none s hsn
  | succ n =>
    rw [List.replicate_succ] at hw
    exact hs ((Option.some_inj.mp hw).symm)

/-- Multiplying by the inverse generator detects the complementary head letter. -/
private theorem btFree_mem_inv_mul (x : Fin 2) (v : FreeGroup (Fin 2)) :
    (FreeGroup.of x)⁻¹ * v ∈ btW (x, false) ↔ v ∉ btW (x, true) := by
  simp only [btW, Set.mem_ofPred_eq, btInv_of, FreeGroup.toWord_mk_mul_eq,
    Bool.not_false]
  match hv : v.toWord with
  | [] =>
    simp
  | hd :: tl =>
    by_cases heq : hd = (x, true)
    · have hc : ((hd :: tl).head? = some (x, true)) := by
        rw [heq, List.head?_cons]
      rw [ite_eq_left hc, hc, eq_self_iff_true, not_true_eq_false, iff_false]
      cases tl with
      | nil =>
        intro h
        exact Option.some_ne_none _ h.symm
      | cons hd2 tl2 =>
        have hred : FreeGroup.IsReduced ((x, true) :: hd2 :: tl2) := by
          rw [← heq, ← hv]
          exact FreeGroup.isReduced_toWord
        have hstep := (FreeGroup.isReduced_cons_cons).mp hred
        intro hcon
        have hd2eq : hd2 = (x, false) := Option.some_inj.mp hcon
        rw [hd2eq] at hstep
        have hcontra := hstep.1 rfl
        simp at hcontra
    · have hne2 : (hd :: tl).head? ≠ some (x, true) := by
        intro h
        apply heq
        have h2 : (some hd : Option (Fin 2 × Bool)) = some (x, true) := h
        exact Option.some_inj.mp h2
      rw [ite_eq_right hne2]
      exact iff_of_true List.head?_cons hne2

/-- The four pieces are pairwise disjoint and cover the group. -/
private theorem btFree_pieces :
    Disjoint btP₁ btP₂ ∧ Disjoint btP₁ btP₃ ∧ Disjoint btP₁ btP₄ ∧
    Disjoint btP₂ btP₃ ∧ Disjoint btP₂ btP₄ ∧ Disjoint btP₃ btP₄ ∧
    btP₁ ∪ btP₂ ∪ btP₃ ∪ btP₄ = Set.univ := by
  have dWW1 : Disjoint (btW (0, true)) (btW (0, false)) :=
    btW_disjoint (by decide)
  have dWW2 : Disjoint (btW (0, true)) (btW (1, true)) :=
    btW_disjoint (by decide)
  have dWW3 : Disjoint (btW (0, true)) (btW (1, false)) :=
    btW_disjoint (by decide)
  have dWW4 : Disjoint (btW (0, false)) (btW (1, true)) :=
    btW_disjoint (by decide)
  have dWW5 : Disjoint (btW (0, false)) (btW (1, false)) :=
    btW_disjoint (by decide)
  have dWW6 : Disjoint (btW (1, true)) (btW (1, false)) :=
    btW_disjoint (by decide)
  have dT1 : Disjoint btT (btW (0, true)) := btT_disjoint_W (by decide)
  have dT3 : Disjoint btT (btW (1, true)) := btT_disjoint_W (by decide)
  have dT4 : Disjoint btT (btW (1, false)) := btT_disjoint_W (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro w hw12 hw2
    simp only [btP₁, Set.mem_union] at hw12
    simp only [btP₂] at hw2
    obtain ⟨hw, hnT⟩ := hw2
    rcases hw12 with hw1 | hT
    · exact Set.disjoint_left.mp dWW1 hw1 hw
    · exact hnT hT
  · rw [Set.disjoint_left]
    intro w hw13 hw3
    simp only [btP₁, Set.mem_union] at hw13
    rcases hw13 with hw1 | hT
    · exact Set.disjoint_left.mp dWW2 hw1 hw3
    · exact Set.disjoint_left.mp dT3 hT hw3
  · rw [Set.disjoint_left]
    intro w hw14 hw4
    simp only [btP₁, Set.mem_union] at hw14
    rcases hw14 with hw1 | hT
    · exact Set.disjoint_left.mp dWW3 hw1 hw4
    · exact Set.disjoint_left.mp dT4 hT hw4
  · rw [Set.disjoint_left]
    intro w hw2 hw3
    simp only [btP₂] at hw2
    obtain ⟨hw, -⟩ := hw2
    exact Set.disjoint_left.mp dWW4 hw hw3
  · rw [Set.disjoint_left]
    intro w hw2 hw4
    simp only [btP₂] at hw2
    obtain ⟨hw, -⟩ := hw2
    exact Set.disjoint_left.mp dWW5 hw hw4
  · exact dWW6
  · rw [Set.eq_univ_iff_forall]
    intro w
    by_cases hw1 : w = 1
    · subst hw1
      have h1T : (1 : FreeGroup (Fin 2)) ∈ btT := ⟨0, by simp⟩
      exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ h1T)))
    · have hne : w.toWord ≠ [] :=
        fun hempty => hw1 (FreeGroup.toWord_eq_nil_iff.mp hempty)
      cases hl : w.toWord with
      | nil => exact absurd hl hne
      | cons hd tl =>
        have hwW : w ∈ btW hd := by
          change w.toWord.head? = some hd
          rw [hl, List.head?_cons]
        obtain ⟨a, b⟩ := hd
        have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
        rcases ha with rfl | rfl <;> cases b
        · by_cases hT : w ∈ btT
          · exact Set.mem_union_left _ (Set.mem_union_left _
              (Set.mem_union_left _ (Set.mem_union_right _ hT)))
          · have hwP2 : w ∈ btP₂ := by
              simp only [btP₂]
              exact ⟨hwW, hT⟩
            exact Set.mem_union_left _ (Set.mem_union_left _
              (Set.mem_union_right _ hwP2))
        · exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
            (Set.mem_union_left _ hwW)))
        · exact Set.mem_union_right _ hwW
        · exact Set.mem_union_left _ (Set.mem_union_right _ hwW)

/-- Left multiplication by the first generator sends `btP₂` onto the complement
of `btP₁`. -/
private theorem btFree_image_P2 :
    (fun w => FreeGroup.of (0 : Fin 2) * w) '' btP₂ = btP₁ᶜ := by
  ext v
  simp only [Set.mem_image, Set.mem_compl_iff]
  constructor
  · rintro ⟨u, huP2, rfl⟩
    simp only [btP₂] at huP2
    obtain ⟨huW, huT⟩ := huP2
    intro hcon
    simp only [btP₁, Set.mem_union, btT, Set.mem_range] at hcon
    rcases hcon with hW | ⟨n, hn⟩
    · have hcancel : (FreeGroup.of (0 : Fin 2))⁻¹ *
          (FreeGroup.of (0 : Fin 2) * u) = u :=
        inv_mul_cancel_left _ _
      have hmem : (FreeGroup.of (0 : Fin 2))⁻¹ *
          (FreeGroup.of (0 : Fin 2) * u) ∈ btW (0, false) := by
        rw [hcancel]
        exact huW
      exact (btFree_mem_inv_mul 0 (FreeGroup.of 0 * u)).mp hmem hW
    · have hu_eq : u = (FreeGroup.of (0 : Fin 2))⁻¹ ^ (n + 1) := by
        have e : (FreeGroup.of (0 : Fin 2))⁻¹ *
            ((FreeGroup.of (0 : Fin 2))⁻¹ ^ n) =
            (FreeGroup.of (0 : Fin 2))⁻¹ ^ (n + 1) :=
          (pow_succ' _ _).symm
        rw [hn] at e
        rw [inv_mul_cancel_left] at e
        exact e
      exact huT ⟨n + 1, hu_eq.symm⟩
  · intro hv
    have hW : v ∉ btW (0, true) := fun h => hv (Set.mem_union_left _ h)
    have hT : v ∉ btT := fun h => hv (Set.mem_union_right _ h)
    have huW : (FreeGroup.of (0 : Fin 2))⁻¹ * v ∈ btW (0, false) :=
      (btFree_mem_inv_mul 0 v).mpr hW
    have huT : (FreeGroup.of (0 : Fin 2))⁻¹ * v ∉ btT := by
      intro hcon
      simp only [btT, Set.mem_range] at hcon
      obtain ⟨n, hn⟩ := hcon
      have hv_eq : v =
          FreeGroup.of (0 : Fin 2) * ((FreeGroup.of (0 : Fin 2))⁻¹ ^ n) := by
        rw [hn]
        exact (mul_inv_cancel_left (FreeGroup.of (0 : Fin 2)) v).symm
      cases n with
      | zero =>
        rw [pow_zero, mul_one] at hv_eq
        apply hW
        rw [hv_eq]
        exact btW_of 0
      | succ n =>
        have e : FreeGroup.of (0 : Fin 2) *
            ((FreeGroup.of (0 : Fin 2))⁻¹ ^ (n + 1)) =
            (FreeGroup.of (0 : Fin 2))⁻¹ ^ n := by
          rw [pow_succ', mul_inv_cancel_left]
        rw [e] at hv_eq
        exact hT ⟨n, hv_eq.symm⟩
    have huP2 : (FreeGroup.of (0 : Fin 2))⁻¹ * v ∈ btP₂ := by
      simp only [btP₂]
      exact ⟨huW, huT⟩
    exact ⟨(FreeGroup.of (0 : Fin 2))⁻¹ * v, huP2, mul_inv_cancel_left _ _⟩

/-- Left multiplication by the second generator sends `btP₄` onto the complement
of `btP₃`. -/
private theorem btFree_image_P4 :
    (fun w => FreeGroup.of (1 : Fin 2) * w) '' btP₄ = btP₃ᶜ := by
  ext v
  simp only [Set.mem_image, Set.mem_compl_iff]
  constructor
  · rintro ⟨u, huP4, rfl⟩
    have hcancel : (FreeGroup.of (1 : Fin 2))⁻¹ *
        (FreeGroup.of (1 : Fin 2) * u) = u :=
      inv_mul_cancel_left _ _
    have hmem : (FreeGroup.of (1 : Fin 2))⁻¹ *
        (FreeGroup.of (1 : Fin 2) * u) ∈ btW (1, false) := by
      rw [hcancel]
      exact huP4
    exact (btFree_mem_inv_mul 1 (FreeGroup.of 1 * u)).mp hmem
  · intro hv
    have hW : v ∉ btW (1, true) := hv
    have huW : (FreeGroup.of (1 : Fin 2))⁻¹ * v ∈ btW (1, false) :=
      (btFree_mem_inv_mul 1 v).mpr hW
    exact ⟨(FreeGroup.of (1 : Fin 2))⁻¹ * v, huW, mul_inv_cancel_left _ _⟩

/-- The inverse action undoes the action. -/
private theorem btAct_inv (w : FreeGroup (Fin 2)) (x : btE) :
    btAct w⁻¹ (btAct w x) = x := by
  rw [← btAct_mul, inv_mul_cancel, btAct_one]

/-- The orbit relation of the action on the free locus. -/
private def btOrbitRel : Setoid {x : btE // x ∈ btOmega} where
  r x y := ∃ w : FreeGroup (Fin 2), btAct w x.val = y.val
  iseqv := {
    refl := fun x => ⟨1, by simp [btAct_one x.val]⟩
    symm := fun {x y} h => by
      obtain ⟨w, hw⟩ := h
      refine ⟨w⁻¹, ?_⟩
      have e := btAct_inv w x.val
      rw [hw] at e
      exact e
    trans := fun {x y z} h1 h2 => by
      obtain ⟨w1, hw1⟩ := h1
      obtain ⟨w2, hw2⟩ := h2
      refine ⟨w2 * w1, ?_⟩
      rw [btAct_mul, hw1, hw2] }

/-- Orbit representative. -/
private noncomputable def btRep (x : {x : btE // x ∈ btOmega}) : {x : btE // x ∈ btOmega} :=
  Quotient.out (Quotient.mk btOrbitRel x)

/-- The representative is related to `x`. -/
private theorem btRep_mem (x : {x : btE // x ∈ btOmega}) :
    ∃ w : FreeGroup (Fin 2), btAct w (btRep x).val = x.val :=
  Quotient.mk_out (s := btOrbitRel) x

/-- Group element moving the representative to `x`. -/
private noncomputable def btGamma (x : {x : btE // x ∈ btOmega}) : FreeGroup (Fin 2) :=
  Classical.choose (btRep_mem x)

/-- The chosen element moves the representative to `x`. -/
private theorem btGamma_spec (x : {x : btE // x ∈ btOmega}) :
    btAct (btGamma x) (btRep x).val = x.val :=
  Classical.choose_spec (btRep_mem x)

/-- Same orbit implies same representative. -/
private theorem btRep_orbit (x y : {x : btE // x ∈ btOmega})
    (h : ∃ w : FreeGroup (Fin 2), btAct w x.val = y.val) : btRep x = btRep y := by
  unfold btRep
  rw [Quotient.sound (s := btOrbitRel) h]

/-- The free locus acts freely. -/
private theorem btOmega_free (x : btE) (hx : x ∈ btOmega)
    (w v : FreeGroup (Fin 2)) (h : btAct w x = btAct v x) : w = v := by
  have hfix : btAct (v⁻¹ * w) x = x := by
    have e1 : btAct (v⁻¹ * w) x = btAct v⁻¹ (btAct w x) := btAct_mul _ _ _
    rw [e1, h]
    exact btAct_inv v x
  by_cases huv : v⁻¹ * w = 1
  · have e : v * (v⁻¹ * w) = v * 1 := congrArg (v * ·) huv
    rw [mul_inv_cancel_left, mul_one] at e
    exact e
  · exfalso
    simp only [btOmega] at hx
    obtain ⟨-, hnb⟩ := hx
    have hx0 : x ≠ 0 := fun hz => hnb (Or.inl hz)
    exact hnb (Or.inr ⟨hx0, v⁻¹ * w, huv, hfix⟩)

/-- The free locus is invariant. -/
private theorem btOmega_invariant (w : FreeGroup (Fin 2))
    (x : btE) (hx : x ∈ btOmega) : btAct w x ∈ btOmega := by
  simp only [btOmega] at hx ⊢
  obtain ⟨hxB, hxn⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    change ‖btIsoOfUnitary (btRho w) x‖ ≤ 1
    rw [btIsoOfUnitary_norm]
    rw [Metric.mem_closedBall, dist_zero_right] at hxB
    exact hxB
  · simp only [Set.mem_union, Set.mem_singleton_iff] at hxn ⊢
    intro hcon
    rcases hcon with h0 | hbad
    · have hx0 : x = 0 := by
        have e := btAct_inv w x
        rw [h0] at e
        have e0 : btAct w⁻¹ (0 : btE) = 0 := btIsoOfUnitary_zero _
        rw [e0] at e
        exact e.symm
      exact (fun hz => hxn (Or.inl hz)) hx0
    · simp only [btBad, Set.mem_ofPred_eq] at hbad
      obtain ⟨-, h, hh, hfix⟩ := hbad
      have hconj : btAct (w⁻¹ * h * w) x = x := by
        rw [btAct_mul, btAct_mul, hfix]
        exact btAct_inv w x
      have hne1 : w⁻¹ * h * w ≠ 1 := by
        intro hcon1
        have e : w * (w⁻¹ * h * w) * w⁻¹ = h := by group
        rw [hcon1] at e
        simp at e
        exact hh e.symm
      have hx0 : x ≠ 0 := fun hz => hxn (Or.inl hz)
      exact hxn (Or.inr ⟨hx0, w⁻¹ * h * w, hne1, hconj⟩)

/-- The cocycle identity. -/
private theorem btGamma_act (h : FreeGroup (Fin 2)) (x : {x : btE // x ∈ btOmega})
    (hx : btAct h x.val ∈ btOmega) :
    btGamma ⟨btAct h x.val, hx⟩ = h * btGamma x := by
  have hrep : btRep ⟨btAct h x.val, hx⟩ = btRep x :=
    (btRep_orbit x ⟨btAct h x.val, hx⟩ ⟨h, rfl⟩).symm
  have h1 := btGamma_spec ⟨btAct h x.val, hx⟩
  have h2 := btGamma_spec x
  have h3 : btAct (h * btGamma x) (btRep ⟨btAct h x.val, hx⟩).val =
      btAct h x.val := by
    rw [btAct_mul, hrep, h2]
  have hfree := btOmega_free (btRep ⟨btAct h x.val, hx⟩).val
    (btRep ⟨btAct h x.val, hx⟩).property _ _ (h1.trans h3.symm)
  exact hfree

/-- The four orbit pieces of the free locus. -/
private def btQ₁ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₁}

private def btQ₂ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₂}

private def btQ₃ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₃}

private def btQ₄ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₄}

/-- The free locus duplicates: each half is congruent to the whole. -/
private theorem btOmega_halves :
    btCongr (btQ₁ ∪ btQ₂) btOmega ∧
    btCongr (btQ₃ ∪ btQ₄) btOmega ∧
    Disjoint (btQ₁ ∪ btQ₂) (btQ₃ ∪ btQ₄) ∧
    (btQ₁ ∪ btQ₂) ∪ (btQ₃ ∪ btQ₄) = btOmega := by
  have hQ1 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₁ ↔ btGamma ⟨x, hx⟩ ∈ btP₁ := by
    intro x hx
    simp only [btQ₁, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hQ2 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₂ ↔ btGamma ⟨x, hx⟩ ∈ btP₂ := by
    intro x hx
    simp only [btQ₂, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hQ3 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₃ ↔ btGamma ⟨x, hx⟩ ∈ btP₃ := by
    intro x hx
    simp only [btQ₃, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hQ4 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₄ ↔ btGamma ⟨x, hx⟩ ∈ btP₄ := by
    intro x hx
    simp only [btQ₄, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hsub1 : btQ₁ ⊆ btOmega := by
    intro x hx
    simp only [btQ₁, Set.mem_ofPred_eq] at hx
    exact hx.1
  have hsub2 : btQ₂ ⊆ btOmega := by
    intro x hx
    simp only [btQ₂, Set.mem_ofPred_eq] at hx
    exact hx.1
  have hsub3 : btQ₃ ⊆ btOmega := by
    intro x hx
    simp only [btQ₃, Set.mem_ofPred_eq] at hx
    exact hx.1
  have hsub4 : btQ₄ ⊆ btOmega := by
    intro x hx
    simp only [btQ₄, Set.mem_ofPred_eq] at hx
    exact hx.1
  obtain ⟨d12, d13, d14, d23, d24, d34, hunion⟩ := btFree_pieces
  have himg2 : btAct (FreeGroup.of (0 : Fin 2)) '' btQ₂ = btOmega \ btQ₁ := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hxQ2, rfl⟩
      simp only [btQ₂, Set.mem_ofPred_eq] at hxQ2
      obtain ⟨hxO, hxP⟩ := hxQ2
      have hyO : btAct (FreeGroup.of 0) x ∈ btOmega :=
        btOmega_invariant _ _ hxO
      have hgam : btGamma ⟨btAct (FreeGroup.of 0) x, hyO⟩ =
          FreeGroup.of 0 * btGamma ⟨x, hxO⟩ :=
        btGamma_act (FreeGroup.of 0) ⟨x, hxO⟩ hyO
      refine ⟨hyO, ?_⟩
      intro hyQ1
      have hP1 : btGamma ⟨btAct (FreeGroup.of 0) x, hyO⟩ ∈ btP₁ :=
        (hQ1 _ hyO).mp hyQ1
      rw [hgam] at hP1
      have hcompl : FreeGroup.of (0 : Fin 2) * btGamma ⟨x, hxO⟩ ∈ btP₁ᶜ := by
        rw [← btFree_image_P2]
        exact ⟨btGamma ⟨x, hxO⟩, hxP, rfl⟩
      exact hcompl hP1
    · rintro ⟨hyO, hyQ1⟩
      have hP1 : btGamma ⟨y, hyO⟩ ∉ btP₁ :=
        fun hP => hyQ1 ((hQ1 y hyO).mpr hP)
      have himg : btGamma ⟨y, hyO⟩ ∈
          (fun w => FreeGroup.of (0 : Fin 2) * w) '' btP₂ := by
        rw [btFree_image_P2]
        exact hP1
      obtain ⟨u, huP2, hu_eq⟩ := himg
      have hxO : btAct (FreeGroup.of (0 : Fin 2))⁻¹ y ∈ btOmega :=
        btOmega_invariant _ _ hyO
      have hgamx : btGamma ⟨btAct (FreeGroup.of (0 : Fin 2))⁻¹ y, hxO⟩ =
          (FreeGroup.of (0 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ :=
        btGamma_act (FreeGroup.of (0 : Fin 2))⁻¹ ⟨y, hyO⟩ hxO
      have hu_eq2 : (FreeGroup.of (0 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ = u := by
        rw [← hu_eq, inv_mul_cancel_left]
      have hxQ2 : btAct (FreeGroup.of (0 : Fin 2))⁻¹ y ∈ btQ₂ := by
        rw [hQ2 _ hxO, hgamx, hu_eq2]
        exact huP2
      refine ⟨btAct (FreeGroup.of (0 : Fin 2))⁻¹ y, hxQ2, ?_⟩
      rw [← btAct_mul, mul_inv_cancel, btAct_one]
  have himg4 : btAct (FreeGroup.of (1 : Fin 2)) '' btQ₄ = btOmega \ btQ₃ := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hxQ4, rfl⟩
      simp only [btQ₄, Set.mem_ofPred_eq] at hxQ4
      obtain ⟨hxO, hxP⟩ := hxQ4
      have hyO : btAct (FreeGroup.of 1) x ∈ btOmega :=
        btOmega_invariant _ _ hxO
      have hgam : btGamma ⟨btAct (FreeGroup.of 1) x, hyO⟩ =
          FreeGroup.of 1 * btGamma ⟨x, hxO⟩ :=
        btGamma_act (FreeGroup.of 1) ⟨x, hxO⟩ hyO
      refine ⟨hyO, ?_⟩
      intro hyQ3
      have hP3 : btGamma ⟨btAct (FreeGroup.of 1) x, hyO⟩ ∈ btP₃ :=
        (hQ3 _ hyO).mp hyQ3
      rw [hgam] at hP3
      have hcompl : FreeGroup.of (1 : Fin 2) * btGamma ⟨x, hxO⟩ ∈ btP₃ᶜ := by
        rw [← btFree_image_P4]
        exact ⟨btGamma ⟨x, hxO⟩, hxP, rfl⟩
      exact hcompl hP3
    · rintro ⟨hyO, hyQ3⟩
      have hP3 : btGamma ⟨y, hyO⟩ ∉ btP₃ :=
        fun hP => hyQ3 ((hQ3 y hyO).mpr hP)
      have himg : btGamma ⟨y, hyO⟩ ∈
          (fun w => FreeGroup.of (1 : Fin 2) * w) '' btP₄ := by
        rw [btFree_image_P4]
        exact hP3
      obtain ⟨u, huP4, hu_eq⟩ := himg
      have hxO : btAct (FreeGroup.of (1 : Fin 2))⁻¹ y ∈ btOmega :=
        btOmega_invariant _ _ hyO
      have hgamx : btGamma ⟨btAct (FreeGroup.of (1 : Fin 2))⁻¹ y, hxO⟩ =
          (FreeGroup.of (1 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ :=
        btGamma_act (FreeGroup.of (1 : Fin 2))⁻¹ ⟨y, hyO⟩ hxO
      have hu_eq2 : (FreeGroup.of (1 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ = u := by
        rw [← hu_eq, inv_mul_cancel_left]
      have hxQ4 : btAct (FreeGroup.of (1 : Fin 2))⁻¹ y ∈ btQ₄ := by
        rw [hQ4 _ hxO, hgamx, hu_eq2]
        exact huP4
      refine ⟨btAct (FreeGroup.of (1 : Fin 2))⁻¹ y, hxQ4, ?_⟩
      rw [← btAct_mul, mul_inv_cancel, btAct_one]
  have hunion1 : btQ₁ ∪ (btOmega \ btQ₁) = btOmega := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (hx | ⟨hxO, -⟩)
      · exact hsub1 hx
      · exact hxO
    · intro hxO
      by_cases hx : x ∈ btQ₁
      · exact Or.inl hx
      · exact Or.inr ⟨hxO, hx⟩
  have hunion3 : btQ₃ ∪ (btOmega \ btQ₃) = btOmega := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (hx | ⟨hxO, -⟩)
      · exact hsub3 hx
      · exact hxO
    · intro hxO
      by_cases hx : x ∈ btQ₃
      · exact Or.inl hx
      · exact Or.inr ⟨hxO, hx⟩
  have dA : Disjoint btQ₁ btQ₂ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have hxO : x ∈ btOmega := hsub1 hx1
    exact Set.disjoint_left.mp d12 ((hQ1 x hxO).mp hx1) ((hQ2 x hxO).mp hx2)
  have dC : Disjoint btQ₃ btQ₄ := by
    rw [Set.disjoint_left]
    intro x hx3 hx4
    have hxO : x ∈ btOmega := hsub3 hx3
    exact Set.disjoint_left.mp d34 ((hQ3 x hxO).mp hx3) ((hQ4 x hxO).mp hx4)
  have hcongr12 : btCongr (btQ₁ ∪ btQ₂) btOmega := by
    have h1 := btCongr_refl btQ₁
    have h2 := btCongr_self_image (btAct (FreeGroup.of (0 : Fin 2))) btQ₂
    rw [himg2] at h2
    have dB : Disjoint btQ₁ (btOmega \ btQ₁) := by
      rw [Set.disjoint_left]
      intro x hx1 hxD
      obtain ⟨-, hnQ1⟩ := hxD
      exact hnQ1 hx1
    have hun := btCongr_union h1 h2 dA dB
    rw [hunion1] at hun
    exact hun
  have hcongr34 : btCongr (btQ₃ ∪ btQ₄) btOmega := by
    have h1 := btCongr_refl btQ₃
    have h2 := btCongr_self_image (btAct (FreeGroup.of (1 : Fin 2))) btQ₄
    rw [himg4] at h2
    have dB : Disjoint btQ₃ (btOmega \ btQ₃) := by
      rw [Set.disjoint_left]
      intro x hx3 hxD
      obtain ⟨-, hnQ3⟩ := hxD
      exact hnQ3 hx3
    have hun := btCongr_union h1 h2 dC dB
    rw [hunion3] at hun
    exact hun
  refine ⟨hcongr12, hcongr34, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx12 hx34
    simp only [Set.mem_union] at hx12 hx34
    have hxO : x ∈ btOmega := by
      rcases hx12 with hx1 | hx2
      · exact hsub1 hx1
      · exact hsub2 hx2
    rcases hx12 with hx1 | hx2 <;> rcases hx34 with hx3 | hx4
    · exact Set.disjoint_left.mp d13 ((hQ1 x hxO).mp hx1) ((hQ3 x hxO).mp hx3)
    · exact Set.disjoint_left.mp d14 ((hQ1 x hxO).mp hx1) ((hQ4 x hxO).mp hx4)
    · exact Set.disjoint_left.mp d23 ((hQ2 x hxO).mp hx2) ((hQ3 x hxO).mp hx3)
    · exact Set.disjoint_left.mp d24 ((hQ2 x hxO).mp hx2) ((hQ4 x hxO).mp hx4)
  · ext x
    simp only [Set.mem_union]
    constructor
    · rintro ((hx1 | hx2) | hx3 | hx4)
      · exact hsub1 hx1
      · exact hsub2 hx2
      · exact hsub3 hx3
      · exact hsub4 hx4
    · intro hxO
      have hmem : btGamma ⟨x, hxO⟩ ∈ btP₁ ∪ btP₂ ∪ btP₃ ∪ btP₄ := by
        rw [hunion]
        exact Set.mem_univ _
      simp only [Set.mem_union] at hmem
      rcases hmem with (((h1 | h2) | h3) | h4)
      · exact Or.inl (Or.inl ((hQ1 x hxO).mpr h1))
      · exact Or.inl (Or.inr ((hQ2 x hxO).mpr h2))
      · exact Or.inr (Or.inl ((hQ3 x hxO).mpr h3))
      · exact Or.inr (Or.inr ((hQ4 x hxO).mpr h4))

/-! ## From the free locus back to the ball -/

/-- `ofLp` preserves addition, zero and negation. -/
private theorem btOfLp_add (a b : btE) :
    WithLp.ofLp (a + b) = WithLp.ofLp a + WithLp.ofLp b :=
  map_add (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)) a b

private theorem btOfLp_zero : WithLp.ofLp (0 : btE) = 0 :=
  map_zero (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))

private theorem btOfLp_neg (a : btE) :
    WithLp.ofLp (-a) = -(WithLp.ofLp a) :=
  map_neg (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)) a

/-- Centre of the absorbing rotation for the ball. -/
private noncomputable def btC : btE := WithLp.toLp 2 ![1 / 2, 0, (0 : ℝ)]

/-- Coordinates of the centre. -/
private theorem btC_coords : WithLp.ofLp btC = ![1 / 2, 0, (0 : ℝ)] := by
  simp [btC]

private theorem btC_coord0 : WithLp.ofLp btC 0 = 1 / 2 := by
  simp [btC_coords, Matrix.cons_val_zero]

/-- The norm of the rotation centre. -/
private theorem btC_norm : ‖btC‖ = 1 / 2 := by
  have e0 : btC 0 = (1 / 2 : ℝ) := rfl
  have e1 : btC 1 = (0 : ℝ) := rfl
  have e2 : btC 2 = (0 : ℝ) := rfl
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, e0, e1, e2]
  have h1 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [h1, norm_zero]
  have h2 : (1 / 2 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = (1 / 2) ^ 2 := by ring
  rw [h2]
  exact Real.sqrt_sq (by norm_num)

/-- The absorbing rotation about the vertical line through `btC`. -/
private noncomputable def btSigma : btE ≃ᵢ btE :=
  ((IsometryEquiv.addRight (-btC)).trans
    (btIsoOfUnitary (btRotZ 1))).trans (IsometryEquiv.addRight btC)

/-- Applying `btSigma` is rotation about `btC`. -/
private theorem btSigma_apply (x : btE) :
    btSigma x = btC + btIsoOfUnitary (btRotZ 1) (x + (-btC)) := by
  simp only [btSigma, IsometryEquiv.trans_apply, IsometryEquiv.addRight_apply]
  exact add_comm _ _

/-- Iterates of `btSigma` rotate about `btC` by multiples of the angle. -/
private theorem btSigma_iterate (n : ℕ) (x : btE) :
    (⇑btSigma)^[n] x =
      btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (x + (-btC)) := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    simp only [Nat.cast_zero, zero_mul, btRotZ_zero, btIsoOfUnitary_one]
    abel
  | succ n ih =>
    rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply', ih,
      btSigma_apply]
    have hcan : btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (x + -btC) + -btC =
        btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (x + -btC) := by abel
    rw [hcan]
    have hcast : ((n + 1 : ℕ) : ℝ) * 1 = 1 + (n : ℝ) * 1 := by push_cast; ring
    rw [hcast, btRotZ_add, btIsoOfUnitary_mul]

/-- The ball is congruent to the punctured ball. -/
private theorem btCongr_ball_punctured :
    btCongr (Metric.closedBall (0 : btE) 1) (Metric.closedBall (0 : btE) 1 \ {0}) := by
  have hnorm : ∀ n : ℕ, ‖(⇑btSigma)^[n] 0‖ ≤ 1 := by
    intro n
    rw [btSigma_iterate]
    calc ‖btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC)‖
        ≤ ‖btC‖ + ‖btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC)‖ :=
          norm_add_le _ _
      _ = 1 := by
          rw [btC_norm, btIsoOfUnitary_norm, zero_add, norm_neg, btC_norm]
          norm_num
  have hY : ∀ n : ℕ, (⇑btSigma)^[n] '' ({0} : Set btE) ⊆
      Metric.closedBall (0 : btE) 1 := by
    intro n
    rw [Set.image_singleton, Set.singleton_subset_iff,
      Metric.mem_closedBall, dist_zero_right]
    exact hnorm n
  have hne : ∀ n : ℕ, 1 ≤ n → (⇑btSigma)^[n] 0 ≠ 0 := by
    intro n hn hcon
    have hsum : btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC) = 0 :=
      (btSigma_iterate n 0).symm.trans hcon
    have hfixpt : btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC) = -btC :=
      eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hsum)
    have hMfix : Matrix.mulVec (btRotZ ((n : ℝ) * 1) : Matrix (Fin 3) (Fin 3) ℝ)
        (-(WithLp.ofLp btC)) = -(WithLp.ofLp btC) := by
      have e := congrArg WithLp.ofLp hfixpt
      rw [btIsoOfUnitary_apply, btOfLp_add, btOfLp_zero, btOfLp_neg] at e
      rw [zero_add] at e
      exact e
    have hcos : Real.cos ((n : ℝ) * 1) = 1 := by
      apply btRotZ_fix_cos _ _ hMfix
      intro hcon2
      have hfst := congrArg Prod.fst hcon2
      simp only [Pi.neg_apply, btC_coord0] at hfst
      norm_num at hfst
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
    have hn0 : n ≠ 0 := by omega
    have hnR : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp only [Int.cast_zero, zero_mul] at hk
      rw [mul_one] at hk
      exact hnR hk.symm
    have hpi : Real.pi = ((n : ℕ) : ℝ) / (2 * ((k : ℤ) : ℝ)) := by
      have hkR : ((k : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk0
      rw [eq_div_iff (mul_ne_zero two_ne_zero hkR)]
      have hring : ((k : ℤ) : ℝ) * (2 * Real.pi) = (2 * ((k : ℤ) : ℝ)) * Real.pi :=
        by ring
      rw [hring, mul_one] at hk
      rw [mul_comm]
      exact hk
    have hpi' : Real.pi = ((((n : ℚ) / (2 * (k : ℚ)))) : ℚ) := by
      exact_mod_cast hpi
    exact irrational_pi.ne_rat _ hpi'
  have hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((⇑btSigma)^[n] '' ({0} : Set btE)) {0} := by
    intro n hn
    rw [Set.disjoint_left]
    intro a ha ha0
    obtain ⟨z, hz, rfl⟩ := ha
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact hne n hn ha0
  exact btCongr_absorb btSigma hY hdisj

/-- Signs as a boolean-indexed family. -/
private def btEps : Bool → ℝ := fun b => if b then 1 else -1

/-- Products of Y-rotations act by composing. -/
private theorem btRotY_mulVec (a b : ℝ) (Z : Fin 3 → ℝ) :
    Matrix.mulVec (btRotY a : Matrix (Fin 3) (Fin 3) ℝ)
      (Matrix.mulVec (btRotY b : Matrix (Fin 3) (Fin 3) ℝ) Z) =
      Matrix.mulVec (btRotY (a + b) : Matrix (Fin 3) (Fin 3) ℝ) Z := by
  rw [btRotY_add, Submonoid.coe_mul, Matrix.mulVec_mulVec]

/-- Y-rotations act injectively. -/
private theorem btRotY_inj (a : ℝ) (X Y : Fin 3 → ℝ)
    (hXY : Matrix.mulVec (btRotY a : Matrix (Fin 3) (Fin 3) ℝ) X =
      Matrix.mulVec (btRotY a : Matrix (Fin 3) (Fin 3) ℝ) Y) : X = Y := by
  have e1 := congrArg (Matrix.mulVec (btRotY (-a) : Matrix (Fin 3) (Fin 3) ℝ)) hXY
  rw [btRotY_mulVec, btRotY_mulVec, neg_add_cancel] at e1
  have h0 : ∀ Z : Fin 3 → ℝ,
      Matrix.mulVec (btRotY (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) Z = Z := by
    intro Z
    simp [btRotY_zero]
  simp only [h0] at e1
  exact e1

/-- The axis never has vanishing outer coordinates. -/
private theorem btU_nz_all (w : FreeGroup (Fin 2)) :
    ((btU w) 0, (btU w) 2) ≠ (0, 0) := by
  by_cases hw : w = 1
  · subst hw
    have eU : btU 1 = ![1, 0, (0 : ℝ)] := rfl
    have e0 : ((![1, 0, (0 : ℝ)] : Fin 3 → ℝ)) 0 = 1 := by
      simp [Matrix.cons_val_zero]
    have e2 : ((![1, 0, (0 : ℝ)] : Fin 3 → ℝ)) 2 = 0 := by
      simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [eU, e0, e2]
    simp
  · exact btU_nz w hw

/-- Each bad-angle set for fixed data is countable. -/
private theorem btBadAngle_countable (w v : FreeGroup (Fin 2)) (n : ℕ) (e : Bool)
    (hn : 1 ≤ n) :
    Set.Countable {t : ℝ |
      Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
        btEps e • btU v} := by
  by_cases hemp : ∃ t₁ : ℝ,
      Matrix.mulVec (btRotY ((n : ℝ) * t₁) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
        btEps e • btU v
  · obtain ⟨t₁, ht₁⟩ := hemp
    have hsub : {t : ℝ |
          Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
            btEps e • btU v} ⊆
        Set.range (fun k : ℤ => t₁ + (k : ℝ) * (2 * Real.pi) / (n : ℝ)) := by
      intro t ht
      have hboth : Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          Matrix.mulVec (btRotY ((n : ℝ) * t₁) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) :=
        ht.trans ht₁.symm
      have hsplit : (n : ℝ) * t = (n : ℝ) * t₁ + (n : ℝ) * (t - t₁) := by ring
      have hmat : Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          Matrix.mulVec (btRotY ((n : ℝ) * t₁) : Matrix (Fin 3) (Fin 3) ℝ)
            (Matrix.mulVec (btRotY ((n : ℝ) * (t - t₁)) : Matrix (Fin 3) (Fin 3) ℝ) (btU w)) := by
        rw [hsplit, btRotY_mulVec]
      rw [hmat] at hboth
      have hfix : Matrix.mulVec (btRotY ((n : ℝ) * (t - t₁)) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          btU w :=
        btRotY_inj _ _ _ hboth
      have hcos : Real.cos ((n : ℝ) * (t - t₁)) = 1 :=
        btRotY_fix_cos _ _ hfix (btU_nz_all w)
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
      have hnR : (n : ℝ) ≠ 0 := by
        have hn0 : n ≠ 0 := by omega
        exact_mod_cast hn0
      have htt : t - t₁ = (k : ℝ) * (2 * Real.pi) / (n : ℝ) := by
        rw [eq_div_iff hnR, mul_comm]
        exact hk.symm
      have htt2 : t = t₁ + (k : ℝ) * (2 * Real.pi) / (n : ℝ) := by
        rw [← htt]
        abel
      exact ⟨k, htt2.symm⟩
    exact Set.Countable.mono hsub (Set.countable_range _)
  · rw [Set.eq_empty_of_forall_notMem (fun t ht => hemp ⟨t, ht⟩)]
    exact Set.countable_empty

/-- The bad-angle set with side conditions is countable. -/
private theorem btBadAngle_piece (w v : FreeGroup (Fin 2)) (n : ℕ) (e : Bool) :
    Set.Countable {t : ℝ | w ≠ 1 ∧ v ≠ 1 ∧ 1 ≤ n ∧
      Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
        btEps e • btU v} := by
  by_cases hn : 1 ≤ n
  · exact Set.Countable.mono (fun t ht => ht.2.2.2) (btBadAngle_countable w v n e hn)
  · have hemp : {t : ℝ | w ≠ 1 ∧ v ≠ 1 ∧ 1 ≤ n ∧
        Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          btEps e • btU v} = ∅ :=
      Set.eq_empty_of_forall_notMem (fun t ht => hn ht.2.2.1)
    rw [hemp]
    exact Set.countable_empty

/-- There is an angle avoiding all axis alignments. -/
private theorem btGoodAngle :
    ∃ t : ℝ, ∀ (w v : FreeGroup (Fin 2)), w ≠ 1 → v ≠ 1 → ∀ (n : ℕ), 1 ≤ n →
      ∀ (ε : ℝ), ε = 1 ∨ ε = -1 →
        Matrix.mulVec (btRotY (n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) ≠
          ε • btU v := by
  have hbad : Set.Countable (⋃ (w : FreeGroup (Fin 2)) (v : FreeGroup (Fin 2))
      (n : ℕ) (e : Bool), {t : ℝ | w ≠ 1 ∧ v ≠ 1 ∧ 1 ≤ n ∧
        Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          btEps e • btU v}) :=
    Set.countable_iUnion fun w => Set.countable_iUnion fun v =>
      Set.countable_iUnion fun n => Set.countable_iUnion fun e =>
        btBadAngle_piece w v n e
  obtain ⟨t, ht⟩ := (hbad.dense_compl ℝ).nonempty
  refine ⟨t, ?_⟩
  intro w v hw hv n hn ε hε hcon
  apply ht
  simp only [Set.mem_iUnion]
  by_cases hε1 : ε = 1
  · refine ⟨w, v, n, true, hw, hv, hn, ?_⟩
    rw [hε1] at hcon
    exact hcon
  · have hεm : ε = -1 := Or.resolve_left hε hε1
    refine ⟨w, v, n, false, hw, hv, hn, ?_⟩
    rw [hεm] at hcon
    exact hcon

/-- Y-rotations preserve dot products. -/
private theorem btRotY_dot (θ : ℝ) (u v : Fin 3 → ℝ) :
    dotProduct
        (Matrix.mulVec (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) v) =
      dotProduct u v := by
  have hort : Matrix.transpose (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ)
      * (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp (btRotY θ).2
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hort, Matrix.vecMul_one]

/-- The punctured ball is congruent to the free locus. -/
private theorem btCongr_punctured_omega :
    btCongr (Metric.closedBall (0 : btE) 1 \ {0}) btOmega := by
  obtain ⟨t, ht⟩ := btGoodAngle
  have hset : (Metric.closedBall (0 : btE) 1 \ {0}) \
      (btBad ∩ Metric.closedBall (0 : btE) 1) = btOmega := by
    simp only [btOmega]
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hB, h0⟩, hC⟩
      refine ⟨hB, fun h => ?_⟩
      rcases h with h00 | hBad
      · exact h0 h00
      · exact hC ⟨hBad, hB⟩
    · rintro ⟨hB, h⟩
      refine ⟨⟨hB, fun e => h (Or.inl e)⟩, fun hC => h ?_⟩
      obtain ⟨hBad, -⟩ := hC
      exact Or.inr hBad
  have hY : ∀ n : ℕ, (btIsoOfUnitary (btRotY t))^[n] ''
      (btBad ∩ Metric.closedBall (0 : btE) 1) ⊆
      Metric.closedBall (0 : btE) 1 \ {0} := by
    intro n y hy
    obtain ⟨z, hzC, rfl⟩ := hy
    obtain ⟨hzBad, hzB⟩ := hzC
    simp only [btBad, Set.mem_ofPred_eq] at hzBad
    obtain ⟨hz0, -, -, -⟩ := hzBad
    have hnorm : ‖(btIsoOfUnitary (btRotY t))^[n] z‖ = ‖z‖ := by
      rw [btRotY_iterate t n z]
      exact btIsoOfUnitary_norm _ _
    have hzB' := Metric.mem_closedBall.mp hzB
    rw [dist_zero_right] at hzB'
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, hnorm]
      exact hzB'
    · intro hcon
      apply hz0
      have hz00 : z = 0 := norm_eq_zero.mp (by rw [← hnorm, hcon, norm_zero])
      exact hz00
  have hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint
      ((btIsoOfUnitary (btRotY t))^[n] ''
        (btBad ∩ Metric.closedBall (0 : btE) 1))
      (btBad ∩ Metric.closedBall (0 : btE) 1) := by
    intro n hn
    rw [Set.disjoint_left]
    rintro a ⟨z, hzC, rfl⟩ haC
    obtain ⟨hzBad, -⟩ := hzC
    obtain ⟨haBad, -⟩ := haC
    simp only [btBad, Set.mem_ofPred_eq] at hzBad haBad
    obtain ⟨hz0, w, hw, hwfix⟩ := hzBad
    obtain ⟨-, v, hv, hvfix⟩ := haBad
    obtain ⟨s, hs⟩ := btU_fix w hw z hwfix
    obtain ⟨s', hs'⟩ := btU_fix v hv _ hvfix
    have hs0 : s ≠ 0 := by
      intro h0
      apply hz0
      have hz00 : WithLp.ofLp z = 0 := by rw [hs, h0, zero_smul]
      apply WithLp.ofLp_injective
      exact hz00.trans btOfLp_zero.symm
    have hcoord : WithLp.ofLp ((btIsoOfUnitary (btRotY t))^[n] z) =
        Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ)
          (WithLp.ofLp z) := by
      rw [btRotY_iterate t n z]
      exact btIsoOfUnitary_apply _ _
    have heq : s • Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ)
        (btU w) = s' • btU v := by
      rw [hs] at hcoord
      rw [Matrix.mulVec_smul] at hcoord
      rw [hs'] at hcoord
      exact hcoord.symm
    have hMw : dotProduct
        (Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w))
        (Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w)) =
        1 := by
      rw [btRotY_dot, btU_dot w hw]
    have hss : s * s = s' * s' := by
      have e1 : dotProduct
          (s • Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w))
          (s • Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w)) =
          dotProduct (s' • btU v) (s' • btU v) := by rw [heq]
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hMw,
        btU_dot v hv, mul_one] at e1
      exact e1
    have hs0' : s' ≠ 0 := by
      intro h0
      have h := mul_ne_zero hs0 hs0
      rw [hss, h0, mul_zero] at h
      exact h rfl
    have hεsq : (s' / s) * (s' / s) = 1 := by
      rw [div_mul_div_comm, hss]
      exact div_self (mul_ne_zero hs0' hs0')
    have hε12 : s' / s = 1 ∨ s' / s = -1 :=
      (mul_self_eq_mul_self_iff (a := s' / s) (b := 1)).mp
        (by rw [hεsq, mul_one])
    have hfin : Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ)
        (btU w) = (s' / s) • btU v := by
      have e := congrArg ((s⁻¹) • ·) heq
      rw [← mul_smul, ← mul_smul, inv_mul_cancel₀ hs0, one_smul] at e
      have hss' : s⁻¹ * s' = s' / s := by rw [div_eq_mul_inv]; ring
      rw [← hss']
      exact e
    exact ht w v hw hv n hn (s' / s) hε12 hfin
  have h := btCongr_absorb (btIsoOfUnitary (btRotY t)) hY hdisj
  rw [hset] at h
  exact h

/-- Second centre at distance 3 on the x-axis. -/
private def btC₂ : btE := WithLp.toLp 2 ![3, 0, (0 : ℝ)]

/-- Translation by the second centre. -/
private noncomputable def btShift : btE ≃ᵢ btE := IsometryEquiv.addRight btC₂

/-- The norm of the second centre. -/
private theorem btC₂_norm : ‖btC₂‖ = 3 := by
  have e0 : btC₂ 0 = (3 : ℝ) := rfl
  have e1 : btC₂ 1 = (0 : ℝ) := rfl
  have e2 : btC₂ 2 = (0 : ℝ) := rfl
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, e0, e1, e2]
  have h1 : ‖(3 : ℝ)‖ = 3 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [h1, norm_zero]
  have h2 : (3 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 3 ^ 2 := by ring
  rw [h2]
  exact Real.sqrt_sq (by norm_num)

/-- The distance between the two centres. -/
private theorem btC₂_dist : dist (0 : btE) btC₂ = 3 := by
  rw [dist_comm, dist_zero_right, btC₂_norm]

/-- The ball duplicates. -/
private theorem btCongr_ball_double :
    btCongr (Metric.closedBall (0 : btE) 1)
        (Metric.closedBall (0 : btE) 1 ∪ btShift '' Metric.closedBall (0 : btE) 1) ∧
      btShift '' Metric.closedBall (0 : btE) 1 = Metric.closedBall btC₂ 1 ∧
      Disjoint (Metric.closedBall (0 : btE) 1)
        (btShift '' Metric.closedBall (0 : btE) 1) := by
  have himg : btShift '' Metric.closedBall (0 : btE) 1 =
      Metric.closedBall btC₂ 1 := by
    have e : btShift (0 : btE) = btC₂ := by
      simp only [btShift, IsometryEquiv.addRight_apply, zero_add]
    rw [IsometryEquiv.image_closedBall, e]
  have hdisj : Disjoint (Metric.closedBall (0 : btE) 1)
      (btShift '' Metric.closedBall (0 : btE) 1) := by
    rw [himg]
    apply Metric.closedBall_disjoint_closedBall
    rw [btC₂_dist]
    norm_num
  have hBallOm : btCongr (Metric.closedBall (0 : btE) 1) btOmega :=
    btCongr_trans btCongr_ball_punctured btCongr_punctured_omega
  obtain ⟨h12, h34, hdisjQ, hunion⟩ := btOmega_halves
  have hQ12B : btCongr (btQ₁ ∪ btQ₂) (Metric.closedBall (0 : btE) 1) :=
    btCongr_trans h12 (btCongr_symm hBallOm)
  have hQ34S : btCongr (btQ₃ ∪ btQ₄)
      (btShift '' Metric.closedBall (0 : btE) 1) :=
    btCongr_trans h34
      (btCongr_trans (btCongr_symm hBallOm)
        (btCongr_self_image btShift (Metric.closedBall (0 : btE) 1)))
  have hOmDouble : btCongr btOmega
      (Metric.closedBall (0 : btE) 1 ∪
        btShift '' Metric.closedBall (0 : btE) 1) := by
    have hun := btCongr_union hQ12B hQ34S hdisjQ hdisj
    rw [hunion] at hun
    exact hun
  exact ⟨btCongr_trans hBallOm hOmDouble, himg, hdisj⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

@[expose] public section

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- **Finite equidecomposability by isometries.** Let $X$ be a metric space. Subsets $A$ and $B$
of $X$ are finitely equidecomposable by isometries if there are a natural number $n$, sets
$A_1, \dots, A_n$ and $B_1, \dots, B_n$ in $X$, and isometric bijections $g_1, \dots, g_n$ of
$X$ onto itself such that the sets $A_i$ are pairwise disjoint, the sets $B_i$ are pairwise
disjoint, $A = A_1 \cup \dots \cup A_n$, $B = B_1 \cup \dots \cup B_n$, and $g_i(A_i) = B_i$
for every $i$. -/
def FinitelyEquidecomposableByIsometries
    {X : Type*} [MetricSpace X] (A B : Set X) : Prop :=
  ∃ (n : ℕ) (As : Fin n → Set X) (Bs : Fin n → Set X) (gs : Fin n → X ≃ᵢ X),
    (∀ i j, i ≠ j → Disjoint (As i) (As j)) ∧
    (∀ i j, i ≠ j → Disjoint (Bs i) (Bs j)) ∧
    (⋃ i, As i) = A ∧
    (⋃ i, Bs i) = B ∧
    ∀ i, (gs i : X → X) '' As i = Bs i

/-- The bijection form converts to the indexed-pieces form. -/
private theorem btCongr_toWanted {X : Type*} [MetricSpace X] {A B : Set X}
    (h : btCongr A B) : FinitelyEquidecomposableByIsometries A B := by
  obtain ⟨f, S, hfin, hbij, hloc⟩ := h
  classical
  by_cases hS : S.Nonempty
  · have := hfin.fintype
    set n := Fintype.card ↥S with hn
    set e := Fintype.equivFin ↥S with he
    obtain ⟨g0, hg0⟩ := hS
    set i0 : Fin n := e ⟨g0, hg0⟩ with hi0
    set gs : Fin n → X ≃ᵢ X := fun i => (e.symm i).val with hgs
    have ch : ∀ x : {x // x ∈ A}, ∃ i : Fin n, f x.val = gs i x.val := by
      intro x
      obtain ⟨g, hgS, hgx⟩ := hloc x.val x.property
      refine ⟨e ⟨g, hgS⟩, ?_⟩
      change f x.val = ((e.symm (e ⟨g, hgS⟩)).val) x.val
      rw [Equiv.symm_apply_apply]
      exact hgx
    set idx : X → Fin n := fun x =>
      if h : x ∈ A then Classical.choose (ch ⟨x, h⟩) else i0 with hidx
    have hidx_eq : ∀ (x : X) (h : x ∈ A),
        idx x = Classical.choose (ch ⟨x, h⟩) := fun x h => dite_eq_left h
    set As : Fin n → Set X := fun i => {x ∈ A | idx x = i} with hAs
    set Bs : Fin n → Set X := fun i => gs i '' As i with hBs
    have hagree : ∀ (i : Fin n) (x : X), x ∈ As i → f x = gs i x := by
      intro i x hx
      obtain ⟨hxA, hxi⟩ := hx
      have h1 : f x = gs (Classical.choose (ch ⟨x, hxA⟩)) x :=
        Classical.choose_spec (ch ⟨x, hxA⟩)
      rw [← hidx_eq x hxA, hxi] at h1
      exact h1
    have hBs_eq : ∀ i, Bs i = f '' As i := by
      intro i
      change gs i '' As i = f '' As i
      exact Set.image_congr (fun x hx => (hagree i x hx).symm)
    have hAs_union : (⋃ i, As i) = A := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset (fun i x hx => hx.1)
      · intro x hx
        exact Set.mem_iUnion.mpr ⟨idx x, hx, rfl⟩
    have hdisjA : ∀ i j, i ≠ j → Disjoint (As i) (As j) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro x ⟨-, hxi⟩ ⟨-, hxj⟩
      exact hij (hxi.symm.trans hxj)
    have hdisjB : ∀ i j, i ≠ j → Disjoint (Bs i) (Bs j) := by
      intro i j hij
      rw [hBs_eq i, hBs_eq j]
      have hsub : ∀ k, As k ⊆ A := fun k x hx => hx.1
      have hinter : f '' As i ∩ f '' As j = ∅ := by
        rw [← hbij.2.1.image_inter (hsub i) (hsub j),
          Set.disjoint_iff_inter_eq_empty.mp (hdisjA i j hij), Set.image_empty]
      exact Set.disjoint_iff_inter_eq_empty.mpr hinter
    have hB_union : (⋃ i, Bs i) = B := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        rw [hBs_eq i] at hi
        obtain ⟨x, hx, hfx⟩ := hi
        subst hfx
        exact hbij.mapsTo (hAs_union ▸ Set.mem_iUnion.mpr ⟨i, hx⟩)
      · intro y hyB
        rw [← hbij.image_eq] at hyB
        obtain ⟨x, hxA, hfx⟩ := hyB
        rw [← hAs_union] at hxA
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxA
        have hagi := hagree i x hi
        exact Set.mem_iUnion.mpr ⟨i, x, hi, by rw [← hagi]; exact hfx⟩
    exact ⟨n, As, Bs, gs, hdisjA, hdisjB, hAs_union, hB_union, fun i => rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    have hA : A = ∅ := Set.eq_empty_of_forall_notMem (fun x hx => by
      obtain ⟨g, hgS, -⟩ := hloc x hx
      rw [hS] at hgS
      exact hgS)
    have hB : B = ∅ := by
      have himg := hbij.image_eq
      rw [hA, Set.image_empty] at himg
      exact himg.symm
    subst hA
    subst hB
    refine ⟨0, fun _ => ∅, fun _ => ∅, fun _ => IsometryEquiv.refl X,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
    · simp
    · simp
    · intro i
      exact i.elim0

/-- From indexed pieces to the bijection form. -/
private theorem btCongr_ofWanted {X : Type*} [MetricSpace X] {A B : Set X}
    (h : FinitelyEquidecomposableByIsometries A B) : btCongr A B := by
  classical
  obtain ⟨n, As, Bs, gs, hdisjA, hdisjB, hUnionA, hUnionB, himg⟩ := h
  have hex : ∀ x : X, x ∈ A → ∃ i, x ∈ As i := by
    intro x hx
    rw [← hUnionA] at hx
    exact Set.mem_iUnion.mp hx
  have hspec : ∀ (x : X) (h : x ∈ A), x ∈ As (Classical.choose (hex x h)) :=
    fun x h => Classical.choose_spec (hex x h)
  have hchoice_eq : ∀ (x : X) (hxA : x ∈ A) (i : Fin n), x ∈ As i →
      Classical.choose (hex x hxA) = i := by
    intro x hxA i hi
    by_contra hne
    exact Set.disjoint_left.mp (hdisjA _ _ hne) (hspec x hxA) hi
  refine ⟨fun x => if h : x ∈ A then gs (Classical.choose (hex x h)) x else x,
    Set.range gs, Set.finite_range gs, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hxA
    simp only [dite_eq_left hxA]
    have hmem : gs (Classical.choose (hex x hxA)) x ∈
        gs (Classical.choose (hex x hxA)) '' As (Classical.choose (hex x hxA)) :=
      ⟨x, hspec x hxA, rfl⟩
    rw [himg] at hmem
    rw [← hUnionB]
    exact Set.mem_iUnion.mpr ⟨_, hmem⟩
  · intro x hxA y hyA hxy
    simp only [dite_eq_left hxA, dite_eq_left hyA] at hxy
    have hxBs : gs (Classical.choose (hex x hxA)) x ∈
        Bs (Classical.choose (hex x hxA)) := by
      have hmem : gs (Classical.choose (hex x hxA)) x ∈
          gs (Classical.choose (hex x hxA)) '' As (Classical.choose (hex x hxA)) :=
        ⟨x, hspec x hxA, rfl⟩
      rwa [himg] at hmem
    have hyBs : gs (Classical.choose (hex y hyA)) y ∈
        Bs (Classical.choose (hex y hyA)) := by
      have hmem : gs (Classical.choose (hex y hyA)) y ∈
          gs (Classical.choose (hex y hyA)) '' As (Classical.choose (hex y hyA)) :=
        ⟨y, hspec y hyA, rfl⟩
      rwa [himg] at hmem
    have hij : Classical.choose (hex x hxA) = Classical.choose (hex y hyA) := by
      by_contra hne
      have hxBs' : gs (Classical.choose (hex y hyA)) y ∈
          Bs (Classical.choose (hex x hxA)) := hxy ▸ hxBs
      exact Set.disjoint_left.mp (hdisjB _ _ hne) hxBs' hyBs
    rw [hij] at hxy
    exact (gs _).injective hxy
  · intro y hyB
    rw [← hUnionB] at hyB
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyB
    rw [← himg i] at hi
    obtain ⟨x, hxAs, hgx⟩ := hi
    have hxmem : x ∈ ⋃ i, As i := Set.mem_iUnion.mpr ⟨i, hxAs⟩
    have hxA : x ∈ A := hUnionA ▸ hxmem
    have hci : Classical.choose (hex x hxA) = i := hchoice_eq x hxA i hxAs
    refine ⟨x, hxA, ?_⟩
    simp only [dite_eq_left hxA]
    rw [hci]
    exact hgx
  · intro x hxA
    exact ⟨gs (Classical.choose (hex x hxA)), Set.mem_range_self _,
      by simp only [dite_eq_left hxA]⟩

/-- **Equidecomposability via piecewise-isometric bijections.** Let $A$ and $B$ be subsets of a
metric space $X$. Then $A$ is finitely equidecomposable by isometries with $B$ if and only if
there are a map $f : X \to X$ and a finite set $S$ of isometric bijections of $X$ onto itself
such that $f$ restricts to a bijection from $A$ onto $B$ and for every $x \in A$ there is
$g \in S$ with $f(x) = g(x)$. -/
public theorem finitelyEquidecomposableByIsometries_iff_bijOn
    {X : Type*} [MetricSpace X] (A B : Set X) :
    FinitelyEquidecomposableByIsometries A B ↔
      ∃ (f : X → X) (S : Set (X ≃ᵢ X)),
        S.Finite ∧ Set.BijOn f A B ∧ ∀ x ∈ A, ∃ g ∈ S, f x = g x := by
  constructor
  · intro h
    exact btCongr_ofWanted h
  · intro h
    exact btCongr_toWanted h

namespace FinitelyEquidecomposableByIsometries

/-- **Finite equidecomposability by isometries is reflexive.** Every subset $A$ of a metric
space $X$ is finitely equidecomposable by isometries with itself. -/
public theorem refl {X : Type*} [MetricSpace X] (A : Set X) :
    FinitelyEquidecomposableByIsometries A A :=
  btCongr_toWanted (btCongr_refl A)

/-- **Finite equidecomposability by isometries is symmetric.** Let $A$ and $B$ be subsets of a
metric space $X$. If $A$ is finitely equidecomposable by isometries with $B$, then $B$ is
finitely equidecomposable by isometries with $A$. -/
public theorem symm {X : Type*} [MetricSpace X] {A B : Set X}
    (h : FinitelyEquidecomposableByIsometries A B) :
    FinitelyEquidecomposableByIsometries B A :=
  btCongr_toWanted (btCongr_symm (btCongr_ofWanted h))

/-- **Finite equidecomposability by isometries is transitive.** Let $A$, $B$ and $C$ be subsets
of a metric space $X$. If $A$ is finitely equidecomposable by isometries with $B$ and $B$ is
finitely equidecomposable by isometries with $C$, then $A$ is finitely equidecomposable by
isometries with $C$. -/
public theorem trans {X : Type*} [MetricSpace X] {A B C : Set X}
    (h1 : FinitelyEquidecomposableByIsometries A B)
    (h2 : FinitelyEquidecomposableByIsometries B C) :
    FinitelyEquidecomposableByIsometries A C :=
  btCongr_toWanted (btCongr_trans (btCongr_ofWanted h1) (btCongr_ofWanted h2))

/-- **Finite equidecomposability by isometries respects disjoint unions.** Let $A_1$, $A_2$,
$B_1$ and $B_2$ be subsets of a metric space $X$ with $A_1 \cap A_2 = \emptyset$ and
$B_1 \cap B_2 = \emptyset$. If $A_1$ is finitely equidecomposable by isometries with $B_1$ and
$A_2$ is finitely equidecomposable by isometries with $B_2$, then $A_1 \cup A_2$ is finitely
equidecomposable by isometries with $B_1 \cup B_2$. -/
public theorem union {X : Type*} [MetricSpace X] {A₁ A₂ B₁ B₂ : Set X}
    (h1 : FinitelyEquidecomposableByIsometries A₁ B₁)
    (h2 : FinitelyEquidecomposableByIsometries A₂ B₂)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂) :
    FinitelyEquidecomposableByIsometries (A₁ ∪ A₂) (B₁ ∪ B₂) :=
  btCongr_toWanted (btCongr_union (btCongr_ofWanted h1) (btCongr_ofWanted h2) hdA hdB)

/-- **Equidecomposability of a set with its isometric image.** Let $g$ be an isometric bijection
of a metric space $X$ onto itself. Then every subset $A$ of $X$ is finitely equidecomposable by
isometries with its image $g(A)$. -/
public theorem image_isometryEquiv {X : Type*} [MetricSpace X]
    (g : X ≃ᵢ X) (A : Set X) :
    FinitelyEquidecomposableByIsometries A (g '' A) :=
  btCongr_toWanted (btCongr_self_image g A)

end FinitelyEquidecomposableByIsometries

/--
**Banach–Tarski paradox for the closed unit ball.** In three-dimensional Euclidean space
$\mathbb{R}^3$, write $\bar B(c, r)$ for the closed ball of radius $r$ about $c$. There are points
$c_1, c_2 \in \mathbb{R}^3$ such that $\bar B(c_1, 1)$ and $\bar B(c_2, 1)$ are disjoint and the
closed unit ball $\bar B(0, 1)$ is finitely equidecomposable by isometries with
$\bar B(c_1, 1) \cup \bar B(c_2, 1)$.

Proves `Wanted` entry `banach_tarski_closedBall_unit`.

Source: S. Banach and A. Tarski, Fund.
Math. 6 (1924) 244–277 original paradox; S. Wagon, The Banach–Tarski Paradox, Cambridge Univ.
Press (1993); Lean states closed unit ball duplication specialization in ℝ³ with ambient `≃ᵢ`
equidecomposability.
-/
public theorem banach_tarski_closedBall_unit :
    ∃ (c₁ c₂ : EuclideanSpace ℝ (Fin 3)),
      Disjoint (Metric.closedBall c₁ 1) (Metric.closedBall c₂ 1) ∧
      FinitelyEquidecomposableByIsometries
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1) := by
  obtain ⟨hcongr, himg, hdisj⟩ := btCongr_ball_double
  refine ⟨0, btC₂, ?_, ?_⟩
  · rw [← himg]
    exact hdisj
  · have h := btCongr_toWanted hcongr
    rw [himg] at h
    exact h

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
