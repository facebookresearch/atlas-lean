/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Reindex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibration
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageIntervalRectangle

/-!
# Every-cell form of finite-stage cofibrations

The existing `stageCofibrations C n` predicate records induced cofibrations
only at consecutive cells in the zero row.  Arbitrary simplex reindexing sends
such cells to possibly nonconsecutive cells in an arbitrary row.  This file
therefore isolates the honest stronger precursor
`stageCofibrationsEverywhere C n`, requiring the same pushout packet at every
non-strict triple `i ≤ j ≤ k`.

The every-cell condition specializes to `stageCofibrations`; conversely, the
successor packets paste along the zero row and transport across stage interval
rectangles, so the two predicates are equivalent.  The every-cell form is
preserved by arbitrary simplex reindexing.  This file does not define a
Waldhausen structure on stages or claim that reindexing is Waldhausen exact.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Reindexing evaluates the underlying stage diagram at the reindexed
interval. -/
@[simp]
theorem reindexStage_obj_obj {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C b.len) (x : Ar a.len) :
    ((reindexStage α).obj A).obj.obj x =
      A.obj.obj ((indexFunctor α).obj x) :=
  rfl

/-- Reindexing maps an indexing arrow by first applying the indexing
functor. -/
@[simp]
theorem reindexStage_obj_map {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C b.len) {x y : Ar a.len} (r : x ⟶ y) :
    ((reindexStage α).obj A).obj.map r =
      A.obj.map ((indexFunctor α).map r) :=
  rfl

/-- A reindexed stage morphism has the original component at the reindexed
interval. -/
@[simp]
theorem reindexStage_map_hom_app {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B) (x : Ar a.len) :
    ((reindexStage α).map f).hom.app x =
      f.hom.app ((indexFunctor α).obj x) :=
  rfl

/-- Reindexing sends an interval value to the value at the mapped
interval. -/
@[simp]
theorem reindexStage_obj_interval {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C b.len) {i j : Fin (a.len + 1)} (hij : i ≤ j) :
    ((reindexStage α).obj A).obj.obj (interval i j hij) =
      A.obj.obj
        (interval ((SimplexCategory.Hom.toOrderHom α) i)
          ((SimplexCategory.Hom.toOrderHom α) j)
          ((SimplexCategory.Hom.toOrderHom α).monotone hij)) := by
  rw [reindexStage_obj_obj, indexFunctor_obj_interval]

/-- A reindexed morphism component at an interval is the original component
at the mapped interval. -/
@[simp]
theorem reindexStage_map_hom_app_interval
    {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B)
    {i j : Fin (a.len + 1)} (hij : i ≤ j) :
    ((reindexStage α).map f).hom.app (interval i j hij) =
      f.hom.app
        (interval ((SimplexCategory.Hom.toOrderHom α) i)
          ((SimplexCategory.Hom.toOrderHom α) j)
          ((SimplexCategory.Hom.toOrderHom α).monotone hij)) := by
  change f.hom.app ((indexFunctor α).obj (interval i j hij)) = _
  have e := indexFunctor_obj_interval α hij
  cases e
  rfl

/-- A horizontal map in a reindexed stage is the original horizontal map at
the mapped triple. -/
@[simp]
theorem reindexStage_obj_map_horiz {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C b.len) {i j k : Fin (a.len + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) :
    ((reindexStage α).obj A).obj.map (horiz hij hjk) =
      A.obj.map
        (horiz ((SimplexCategory.Hom.toOrderHom α).monotone hij)
          ((SimplexCategory.Hom.toOrderHom α).monotone hjk)) := by
  change A.obj.map ((indexFunctor α).map (horiz hij hjk)) = _
  exact congrArg A.obj.map (indexFunctor_map_horiz α hij hjk)

/-- The induced-cofibration packet for one cell of a stage morphism.

For `i ≤ j ≤ k`, push out `A(i,j) → A(i,k)` along the component
`A(i,j) → B(i,j)`.  The induced map from that pushout to `B(i,k)` is
required to be a cofibration. -/
def IsStageCofibrationCell {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) : Prop :=
  ∃ (P : C)
    (inl : A.obj.obj (interval i k (hij.trans hjk)) ⟶ P)
    (inr : B.obj.obj (interval i j hij) ⟶ P)
    (d : P ⟶ B.obj.obj (interval i k (hij.trans hjk))),
    IsPushout (A.obj.map (horiz hij hjk))
        (f.hom.app (interval i j hij)) inl inr ∧
      inl ≫ d = f.hom.app (interval i k (hij.trans hjk)) ∧
      inr ≫ d = B.obj.map (horiz hij hjk) ∧
      IsCofibration d

/-- A cell packet is independent of the witnesses for its two inequalities. -/
theorem IsStageCofibrationCell.proof_irrel {n : ℕ} {A B : Stage C n}
    (f : A ⟶ B) {i j k : Fin (n + 1)}
    (hij hij' : i ≤ j) (hjk hjk' : j ≤ k) :
    IsStageCofibrationCell C f hij hjk ↔
      IsStageCofibrationCell C f hij' hjk' := by
  cases Subsingleton.elim hij hij'
  cases Subsingleton.elim hjk hjk'
  rfl

/-- A cell with equal right endpoints has the canonical identity packet. -/
theorem IsStageCofibrationCell.refl
    {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j : Fin (n + 1)} (hij : i ≤ j) (hjj : j ≤ j) :
    IsStageCofibrationCell C f hij hjj := by
  have hI : interval i j (hij.trans hjj) = interval i j hij := by
    exact (Arrow.mk_inj _ _).mpr (Subsingleton.elim _ _)
  let _ : IsIso (horiz hij hjj) := IsIso.mk
    ⟨eqToHom hI,
      by apply Arrow.hom_ext <;> exact Subsingleton.elim _ _,
      by apply Arrow.hom_ext <;> exact Subsingleton.elim _ _⟩
  refine ⟨B.obj.obj (interval i j (hij.trans hjj)),
    f.hom.app (interval i j (hij.trans hjj)),
    B.obj.map (horiz hij hjj), 𝟙 _, ?_, ?_, ?_, ?_⟩
  · exact IsPushout.of_horiz_isIso
      ⟨f.hom.naturality (horiz hij hjj)⟩
  · simp
  · simp
  · exact MorphismProperty.id_mem
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) _

/-- Horizontally adjacent cell packets paste to a packet for their union.

The proof uses the stage cofibration `A(i,k) ⟶ A(i,l)` to choose the upper
pushout square.  `IsPushout.of_top` then identifies the lower square as the
cobase change of the first induced cofibration, so its composite with the
second induced cofibration is again a cofibration. -/
theorem IsStageCofibrationCell.paste_horiz
    {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j k l : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
    (h₁ : IsStageCofibrationCell C f hij hjk)
    (h₂ : IsStageCofibrationCell C f (hij.trans hjk) hkl) :
    IsStageCofibrationCell C f hij (hjk.trans hkl) := by
  obtain ⟨P₁, inl₁, inr₁, d₁, hpush₁, hinl₁, hinr₁, hd₁⟩ := h₁
  obtain ⟨P₂, inl₂, inr₂, d₂, hpush₂, hinl₂, hinr₂, hd₂⟩ := h₂
  have hAcof : IsCofibration
      (A.obj.map (horiz (hij.trans hjk) hkl)) :=
    (A.property.cofiber_triple (hij.trans hjk) hkl).1
  obtain ⟨Q, qP, qA, hupperRaw, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
      (A.obj.map (horiz (hij.trans hjk) hkl)) hAcof P₁ inl₁
  have hupper : IsPushout
      (A.obj.map (horiz (hij.trans hjk) hkl)) inl₁ qA qP :=
    hupperRaw.flip
  have hagree :
      A.obj.map (horiz (hij.trans hjk) hkl) ≫ inl₂ =
        inl₁ ≫ (d₁ ≫ inr₂) := by
    calc
      A.obj.map (horiz (hij.trans hjk) hkl) ≫ inl₂ =
          f.hom.app (interval i k (hij.trans hjk)) ≫ inr₂ := hpush₂.w
      _ = (inl₁ ≫ d₁) ≫ inr₂ := by rw [hinl₁]
      _ = inl₁ ≫ (d₁ ≫ inr₂) := Category.assoc _ _ _
  let e : Q ⟶ P₂ := hupper.desc inl₂ (d₁ ≫ inr₂) hagree
  have hqA : qA ≫ e = inl₂ := hupper.inl_desc _ _ _
  have hqPdesc : qP ≫ e = d₁ ≫ inr₂ := hupper.inr_desc _ _ _
  have houter : IsPushout
      (A.obj.map (horiz (hij.trans hjk) hkl))
      (inl₁ ≫ d₁) (qA ≫ e) inr₂ := by
    rw [hinl₁, hqA]
    exact hpush₂
  have hlower : IsPushout qP d₁ e inr₂ :=
    houter.of_top hqPdesc hupper
  have he : IsCofibration e :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hlower hd₁
  have hed₂ : IsCofibration (e ≫ d₂) :=
    (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem e d₂ he hd₂
  have hAcomp :
      A.obj.map (horiz hij hjk) ≫
          A.obj.map (horiz (hij.trans hjk) hkl) =
        A.obj.map (horiz hij (hjk.trans hkl)) := by
    rw [← A.obj.map_comp]
    apply A.obj.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hBcomp :
      B.obj.map (horiz hij hjk) ≫
          B.obj.map (horiz (hij.trans hjk) hkl) =
        B.obj.map (horiz hij (hjk.trans hkl)) := by
    rw [← B.obj.map_comp]
    apply B.obj.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hpush : IsPushout
      (A.obj.map (horiz hij (hjk.trans hkl)))
      (f.hom.app (interval i j hij)) qA (inr₁ ≫ qP) := by
    rw [← hAcomp]
    exact hpush₁.paste_horiz hupper
  have hinl : qA ≫ (e ≫ d₂) =
      f.hom.app (interval i l (hij.trans (hjk.trans hkl))) := by
    rw [← Category.assoc, hqA, hinl₂]
  have hinr : (inr₁ ≫ qP) ≫ (e ≫ d₂) =
      B.obj.map (horiz hij (hjk.trans hkl)) := by
    calc
      (inr₁ ≫ qP) ≫ (e ≫ d₂) =
          inr₁ ≫ ((qP ≫ e) ≫ d₂) := by simp only [Category.assoc]
      _ = inr₁ ≫ ((d₁ ≫ inr₂) ≫ d₂) := by rw [hqPdesc]
      _ = (inr₁ ≫ d₁) ≫ (inr₂ ≫ d₂) := by simp only [Category.assoc]
      _ = B.obj.map (horiz hij hjk) ≫
          B.obj.map (horiz (hij.trans hjk) hkl) := by rw [hinr₁, hinr₂]
      _ = B.obj.map (horiz hij (hjk.trans hkl)) := hBcomp
  exact ⟨Q, qA, inr₁ ≫ qP, e ≫ d₂, hpush, hinl, hinr, hed₂⟩

/-- Cell packets are closed under composition of stage morphisms. -/
theorem IsStageCofibrationCell.comp
    {n : ℕ} {A B D : Stage C n} (f : A ⟶ B) (g : B ⟶ D)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    (hf : IsStageCofibrationCell C f hij hjk)
    (hg : IsStageCofibrationCell C g hij hjk) :
    IsStageCofibrationCell C (f ≫ g) hij hjk := by
  obtain ⟨P, pA, pB, df, hpushF, hpA, hpB, hdf⟩ := hf
  obtain ⟨Q, qB, qD, dg, hpushG, hqB, hqD, hdg⟩ := hg
  have hAcof : IsCofibration (A.obj.map (horiz hij hjk)) :=
    (A.property.cofiber_triple hij hjk).1
  have hpBcof : IsCofibration pB :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hpushF.flip hAcof
  obtain ⟨R, rD, rP, hR, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) pB hpBcof
      (D.obj.obj (interval i j hij))
      (g.hom.app (interval i j hij))
  have hpush : IsPushout (A.obj.map (horiz hij hjk))
      ((f ≫ g).hom.app (interval i j hij)) (pA ≫ rP) rD := by
    change IsPushout (A.obj.map (horiz hij hjk))
      (f.hom.app (interval i j hij) ≫ g.hom.app (interval i j hij))
      (pA ≫ rP) rD
    exact hpushF.paste_vert hR.flip
  have hagree :
      g.hom.app (interval i j hij) ≫ qD =
        pB ≫ (df ≫ qB) := by
    calc
      g.hom.app (interval i j hij) ≫ qD =
          B.obj.map (horiz hij hjk) ≫ qB := hpushG.w.symm
      _ = (pB ≫ df) ≫ qB := by rw [hpB]
      _ = pB ≫ (df ≫ qB) := Category.assoc _ _ _
  let e : R ⟶ Q := hR.desc qD (df ≫ qB) hagree
  have hrD : rD ≫ e = qD := hR.inl_desc _ _ _
  have hrP : rP ≫ e = df ≫ qB := hR.inr_desc _ _ _
  have houter : IsPushout
      (g.hom.app (interval i j hij)) (pB ≫ df)
      (rD ≫ e) qB := by
    rw [hpB, hrD]
    exact hpushG.flip
  have hlower : IsPushout rP df e qB :=
    houter.of_top hrP hR
  have he : IsCofibration e :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hlower hdf
  have hedg : IsCofibration (e ≫ dg) :=
    (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem e dg he hdg
  have hinl : (pA ≫ rP) ≫ (e ≫ dg) =
      (f ≫ g).hom.app (interval i k (hij.trans hjk)) := by
    change (pA ≫ rP) ≫ (e ≫ dg) =
      f.hom.app (interval i k (hij.trans hjk)) ≫
        g.hom.app (interval i k (hij.trans hjk))
    calc
      (pA ≫ rP) ≫ (e ≫ dg) =
          pA ≫ ((rP ≫ e) ≫ dg) := by simp only [Category.assoc]
      _ = pA ≫ ((df ≫ qB) ≫ dg) := by rw [hrP]
      _ = (pA ≫ df) ≫ (qB ≫ dg) := by simp only [Category.assoc]
      _ = f.hom.app (interval i k (hij.trans hjk)) ≫
          g.hom.app (interval i k (hij.trans hjk)) := by rw [hpA, hqB]
  have hinr : rD ≫ (e ≫ dg) = D.obj.map (horiz hij hjk) := by
    rw [← Category.assoc, hrD, hqD]
  exact ⟨R, pA ≫ rP, rD, e ≫ dg, hpush, hinl, hinr, hedg⟩

/-- A zero-row cell packet transports to the corresponding cell in any
later row. -/
theorem IsStageCofibrationCell.of_zeroRow
    {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    (hzero : IsStageCofibrationCell C f (Fin.zero_le j) hjk) :
    IsStageCofibrationCell C f hij hjk := by
  have h0ij : (0 : Fin (n + 1)) ≤ j :=
    (Fin.zero_le i).trans hij
  have hzero' : IsStageCofibrationCell C f h0ij hjk :=
    (IsStageCofibrationCell.proof_irrel C f
      (Fin.zero_le j) h0ij hjk hjk).mp hzero
  obtain ⟨P₀, a₀, b₀, d₀, hpush₀, ha₀, hb₀, hd₀⟩ := hzero'
  have hA := A.property.isPushout_intervalRectangle
    (Fin.zero_le i) hij hjk
  have hB := B.property.isPushout_intervalRectangle
    (Fin.zero_le i) hij hjk
  have hA0cof : IsCofibration
      (A.obj.map (horiz h0ij hjk)) :=
    (A.property.cofiber_triple h0ij hjk).1
  have hb₀cof : IsCofibration b₀ :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hpush₀.flip hA0cof
  obtain ⟨Q, qBij, qP₀, hQ, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) b₀ hb₀cof
      (B.obj.obj (interval i j hij))
      (B.obj.map (vert (Fin.zero_le i) hij))
  have hagreeA :
      A.obj.map (horiz h0ij hjk) ≫ (a₀ ≫ qP₀) =
        A.obj.map (vert (Fin.zero_le i) hij) ≫
          (f.hom.app (interval i j hij) ≫ qBij) := by
    calc
      A.obj.map (horiz h0ij hjk) ≫ (a₀ ≫ qP₀) =
          (A.obj.map (horiz h0ij hjk) ≫ a₀) ≫ qP₀ :=
        (Category.assoc _ _ _).symm
      _ = (f.hom.app (interval 0 j h0ij) ≫ b₀) ≫ qP₀ := by
        rw [hpush₀.w]
      _ = f.hom.app (interval 0 j h0ij) ≫ (b₀ ≫ qP₀) :=
        Category.assoc _ _ _
      _ = f.hom.app (interval 0 j h0ij) ≫
          (B.obj.map (vert (Fin.zero_le i) hij) ≫ qBij) := by
        rw [hQ.w]
      _ = (f.hom.app (interval 0 j h0ij) ≫
          B.obj.map (vert (Fin.zero_le i) hij)) ≫ qBij :=
        (Category.assoc _ _ _).symm
      _ = (A.obj.map (vert (Fin.zero_le i) hij) ≫
          f.hom.app (interval i j hij)) ≫ qBij := by
        rw [f.hom.naturality]
      _ = A.obj.map (vert (Fin.zero_le i) hij) ≫
          (f.hom.app (interval i j hij) ≫ qBij) :=
        Category.assoc _ _ _
  let qAik : A.obj.obj (interval i k (hij.trans hjk)) ⟶ Q :=
    hA.desc (a₀ ≫ qP₀)
      (f.hom.app (interval i j hij) ≫ qBij) hagreeA
  have hAvk :
      A.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫ qAik =
        a₀ ≫ qP₀ := hA.inl_desc _ _ _
  have hAi :
      A.obj.map (horiz hij hjk) ≫ qAik =
        f.hom.app (interval i j hij) ≫ qBij := hA.inr_desc _ _ _
  have houterA : IsPushout
      (A.obj.map (horiz h0ij hjk))
      (A.obj.map (vert (Fin.zero_le i) hij) ≫
        f.hom.app (interval i j hij))
      (A.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫ qAik)
      qBij := by
    rw [f.hom.naturality, hAvk]
    exact hpush₀.paste_vert hQ.flip
  have hpush : IsPushout
      (A.obj.map (horiz hij hjk))
      (f.hom.app (interval i j hij)) qAik qBij :=
    houterA.of_top hAi hA
  have hagreeB :
      B.obj.map (vert (Fin.zero_le i) hij) ≫
          B.obj.map (horiz hij hjk) =
        b₀ ≫ (d₀ ≫
          B.obj.map (vert (Fin.zero_le i) (hij.trans hjk))) := by
    calc
      B.obj.map (vert (Fin.zero_le i) hij) ≫
          B.obj.map (horiz hij hjk) =
        B.obj.map (horiz h0ij hjk) ≫
          B.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) := hB.w.symm
      _ = (b₀ ≫ d₀) ≫
          B.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) := by rw [hb₀]
      _ = b₀ ≫ (d₀ ≫
          B.obj.map (vert (Fin.zero_le i) (hij.trans hjk))) :=
        Category.assoc _ _ _
  let dQ : Q ⟶ B.obj.obj (interval i k (hij.trans hjk)) :=
    hQ.desc (B.obj.map (horiz hij hjk))
      (d₀ ≫ B.obj.map (vert (Fin.zero_le i) (hij.trans hjk))) hagreeB
  have hqBij : qBij ≫ dQ = B.obj.map (horiz hij hjk) :=
    hQ.inl_desc _ _ _
  have hqP₀ : qP₀ ≫ dQ =
      d₀ ≫ B.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) :=
    hQ.inr_desc _ _ _
  have houterB : IsPushout
      (B.obj.map (vert (Fin.zero_le i) hij)) (b₀ ≫ d₀)
      (qBij ≫ dQ)
      (B.obj.map (vert (Fin.zero_le i) (hij.trans hjk))) := by
    rw [hb₀, hqBij]
    exact hB.flip
  have hlower : IsPushout qP₀ d₀ dQ
      (B.obj.map (vert (Fin.zero_le i) (hij.trans hjk))) :=
    houterB.of_top hqP₀ hQ
  have hdQ : IsCofibration dQ :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hlower hd₀
  have hqAik : qAik ≫ dQ =
      f.hom.app (interval i k (hij.trans hjk)) := by
    apply hA.hom_ext
    · calc
        A.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫
            (qAik ≫ dQ) =
          (A.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫ qAik) ≫ dQ :=
            (Category.assoc _ _ _).symm
        _ = (a₀ ≫ qP₀) ≫ dQ := by rw [hAvk]
        _ = a₀ ≫ (qP₀ ≫ dQ) := Category.assoc _ _ _
        _ = a₀ ≫ (d₀ ≫
            B.obj.map (vert (Fin.zero_le i) (hij.trans hjk))) := by rw [hqP₀]
        _ = (a₀ ≫ d₀) ≫
            B.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) :=
              (Category.assoc _ _ _).symm
        _ = f.hom.app (interval 0 k (h0ij.trans hjk)) ≫
            B.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) := by rw [ha₀]
        _ = A.obj.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫
            f.hom.app (interval i k (hij.trans hjk)) :=
              (f.hom.naturality _).symm
    · calc
        A.obj.map (horiz hij hjk) ≫ (qAik ≫ dQ) =
          (A.obj.map (horiz hij hjk) ≫ qAik) ≫ dQ :=
            (Category.assoc _ _ _).symm
        _ = (f.hom.app (interval i j hij) ≫ qBij) ≫ dQ := by rw [hAi]
        _ = f.hom.app (interval i j hij) ≫ (qBij ≫ dQ) :=
          Category.assoc _ _ _
        _ = f.hom.app (interval i j hij) ≫
            B.obj.map (horiz hij hjk) := by rw [hqBij]
        _ = A.obj.map (horiz hij hjk) ≫
            f.hom.app (interval i k (hij.trans hjk)) :=
              (f.hom.naturality _).symm
  exact ⟨Q, qAik, qBij, dQ, hpush, hqAik, hqBij, hdQ⟩

/-- Every-cell formulation of stage cofibrations.  This is kept as a separate
morphism property from the successor-only `stageCofibrations` so that
reindexing can be stated directly. -/
def stageCofibrationsEverywhere (n : ℕ) : MorphismProperty (Stage C n) :=
  fun _ _ f ↦ ∀ {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k),
    IsStageCofibrationCell C f hij hjk

/-- Membership in `stageCofibrationsEverywhere` is the every-cell packet. -/
theorem mem_stageCofibrationsEverywhere_iff {n : ℕ} {A B : Stage C n}
    (f : A ⟶ B) :
    stageCofibrationsEverywhere C n f ↔
      ∀ {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k),
        IsStageCofibrationCell C f hij hjk :=
  Iff.rfl

/-- Successor-only stage cofibrations supply the cell packet on every
zero-row interval. -/
theorem zeroRowCell_of_stageCofibrations
    {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrations C n f)
    {j k : Fin (n + 1)} (hjk : j ≤ k) :
    IsStageCofibrationCell C f (Fin.zero_le j) hjk := by
  revert j
  induction k using Fin.induction with
  | zero =>
      intro j hjk
      obtain rfl : j = 0 := le_antisymm hjk (Fin.zero_le j)
      exact IsStageCofibrationCell.refl C f (Fin.zero_le _) hjk
  | succ r ih =>
      intro j hjk
      by_cases hj : j = r.succ
      · subst j
        exact IsStageCofibrationCell.refl C f (Fin.zero_le _) hjk
      · have hjr : j ≤ r.castSucc :=
          Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hjk hj)
        have hleft :
            IsStageCofibrationCell C f (Fin.zero_le j) hjr :=
          ih hjr
        have hright : IsStageCofibrationCell C f
            (Fin.zero_le r.castSucc) r.castSucc_le_succ := by
          simpa only [IsStageCofibrationCell, Stage.zeroRowObj,
            Stage.zeroRowSuccMap, Stage.zeroRowApp] using hf r
        have hright' : IsStageCofibrationCell C f
            ((Fin.zero_le j).trans hjr) r.castSucc_le_succ :=
          (IsStageCofibrationCell.proof_irrel C f
            (Fin.zero_le r.castSucc) ((Fin.zero_le j).trans hjr)
            r.castSucc_le_succ r.castSucc_le_succ).mp hright
        have hpaste : IsStageCofibrationCell C f
            (Fin.zero_le j) (hjr.trans r.castSucc_le_succ) :=
          IsStageCofibrationCell.paste_horiz C f
            (Fin.zero_le j) hjr r.castSucc_le_succ hleft hright'
        exact (IsStageCofibrationCell.proof_irrel C f
          (Fin.zero_le j) (Fin.zero_le j)
          (hjr.trans r.castSucc_le_succ) hjk).mp hpaste

/-- Successor-only stage cofibrations propagate to every cell. -/
theorem stageCofibrationsEverywhere_of_stageCofibrations
    {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrations C n f) :
    stageCofibrationsEverywhere C n f := by
  intro i j k hij hjk
  exact IsStageCofibrationCell.of_zeroRow C f hij hjk
    (zeroRowCell_of_stageCofibrations C hf hjk)

/-- Arbitrary simplex reindexing preserves the every-cell cofibration
condition. -/
theorem stageCofibrationsEverywhere_of_reindexStage
    {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B)
    (hf : stageCofibrationsEverywhere C b.len f) :
    stageCofibrationsEverywhere C a.len ((reindexStage α).map f) := by
  intro i j k hij hjk
  have h := hf ((SimplexCategory.Hom.toOrderHom α).monotone hij)
    ((SimplexCategory.Hom.toOrderHom α).monotone hjk)
  have htrans :
      ((SimplexCategory.Hom.toOrderHom α).monotone hij).trans
          ((SimplexCategory.Hom.toOrderHom α).monotone hjk) =
        (SimplexCategory.Hom.toOrderHom α).monotone (hij.trans hjk) :=
    Subsingleton.elim _ _
  cases htrans
  unfold IsStageCofibrationCell at h ⊢
  simp only [reindexStage_map_hom_app_interval,
    reindexStage_obj_map_horiz]
  rcases h with ⟨P, inl, inr, d, hpush, hinl, hinr, hd⟩
  exact ⟨P, inl, inr, d, hpush, hinl, hinr, hd⟩

/-- The every-cell condition specializes to the existing successor-only
stage cofibration condition. -/
theorem stageCofibrations_of_everywhere {n : ℕ} {A B : Stage C n}
    {f : A ⟶ B} (hf : stageCofibrationsEverywhere C n f) :
    stageCofibrations C n f := by
  intro r
  simpa only [IsStageCofibrationCell, Stage.zeroRowObj,
    Stage.zeroRowSuccMap, Stage.zeroRowApp] using
      (hf (Fin.zero_le _) r.castSucc_le_succ)

/-- The successor-only and every-cell formulations of stage cofibrations are
equivalent. -/
theorem stageCofibrationsEverywhere_iff_stageCofibrations
    {n : ℕ} {A B : Stage C n} (f : A ⟶ B) :
    stageCofibrationsEverywhere C n f ↔ stageCofibrations C n f :=
  ⟨stageCofibrations_of_everywhere C,
    stageCofibrationsEverywhere_of_stageCofibrations C⟩

/-- Every interval component of a stage cofibration is a cofibration in the
ambient category. -/
theorem stageCofibrations_app_interval
    {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrations C n f)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsCofibration (f.hom.app (interval i j hij)) := by
  have hfevery : stageCofibrationsEverywhere C n f :=
    stageCofibrationsEverywhere_of_stageCofibrations C hf
  obtain ⟨P, inl, inr, d, hpush, hinl, hinr, hd⟩ :=
    hfevery (le_refl i) hij
  have hAi : IsZero (A.obj.obj (interval i i (le_refl i))) := by
    simpa only [diag] using A.property.diag_isZero i
  have hBi : IsZero (B.obj.obj (interval i i (le_refl i))) := by
    simpa only [diag] using B.property.diag_isZero i
  let _ : IsIso (f.hom.app (interval i i (le_refl i))) :=
    IsZero.isIso hAi hBi _
  let _ : IsIso inl := hpush.isIso_inl_of_isIso
  rw [← hinl]
  exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem inl d
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).of_isIso inl) hd

/-- Every component of a stage cofibration is a cofibration in the ambient
category. -/
theorem stageCofibrations_app
    {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrations C n f) (x : Ar n) :
    IsCofibration (f.hom.app x) := by
  have hx : interval x.left x.right (leOfHom x.hom) = x := by
    rw [← Arrow.mk_eq x]
    exact congrArg Arrow.mk (Subsingleton.elim _ _)
  rw [← hx]
  exact stageCofibrations_app_interval C hf (leOfHom x.hom)

/-- Every isomorphism of stages is a stage cofibration. -/
theorem stageCofibrations_of_isIso
    {n : ℕ} {A B : Stage C n} (f : A ⟶ B) [IsIso f] :
    stageCofibrations C n f := by
  apply stageCofibrations_of_everywhere C
  intro i j k hij hjk
  let _ : IsIso (f.hom.app (interval i j hij)) := by
    change IsIso (((forget C n).map f).app (interval i j hij))
    infer_instance
  let _ : IsIso (f.hom.app (interval i k (hij.trans hjk))) := by
    change IsIso
      (((forget C n).map f).app (interval i k (hij.trans hjk)))
    infer_instance
  refine ⟨B.obj.obj (interval i k (hij.trans hjk)),
    f.hom.app (interval i k (hij.trans hjk)),
    B.obj.map (horiz hij hjk), 𝟙 _, ?_, ?_, ?_, ?_⟩
  · exact IsPushout.of_vert_isIso
      ⟨f.hom.naturality (horiz hij hjk)⟩
  · simp
  · simp
  · exact MorphismProperty.id_mem
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) _

/-- Identity stage morphisms are stage cofibrations. -/
theorem stageCofibrations_id {n : ℕ} (A : Stage C n) :
    stageCofibrations C n (𝟙 A) :=
  stageCofibrations_of_isIso C (𝟙 A)

instance stageCofibrations_containsIdentities (n : ℕ) :
    (stageCofibrations C n).ContainsIdentities where
  id_mem := stageCofibrations_id C

private theorem stageCofibrations_of_arrowIso
    {n : ℕ} (F G : Arrow (Stage C n)) (e : F ≅ G)
    (hF : stageCofibrations C n F.hom) :
    stageCofibrations C n G.hom := by
  apply stageCofibrations_of_everywhere C
  have hFevery : stageCofibrationsEverywhere C n F.hom :=
    stageCofibrationsEverywhere_of_stageCofibrations C hF
  intro i j k hij hjk
  obtain ⟨P, inl, inr, d, hpush, hinl, hinr, hd⟩ := hFevery hij hjk
  let _ : IsIso
      (e.hom.left.hom.app (interval i j hij)) := by
    change IsIso
      (((forget C n).map e.hom.left).app (interval i j hij))
    infer_instance
  let _ : IsIso
      (e.hom.left.hom.app (interval i k (hij.trans hjk))) := by
    change IsIso
      (((forget C n).map e.hom.left).app
        (interval i k (hij.trans hjk)))
    infer_instance
  let _ : IsIso
      (e.hom.right.hom.app (interval i j hij)) := by
    change IsIso
      (((forget C n).map e.hom.right).app (interval i j hij))
    infer_instance
  let _ : IsIso
      (e.hom.right.hom.app (interval i k (hij.trans hjk))) := by
    change IsIso
      (((forget C n).map e.hom.right).app
        (interval i k (hij.trans hjk)))
    infer_instance
  have hsquare (I : Ar n) :
      F.hom.hom.app I ≫ e.hom.right.hom.app I =
        e.hom.left.hom.app I ≫ G.hom.hom.app I := by
    have w := congrArg (fun q : F.left ⟶ G.right => q.hom.app I) e.hom.w
    change e.hom.left.hom.app I ≫ G.hom.hom.app I =
      F.hom.hom.app I ≫ e.hom.right.hom.app I at w
    exact w.symm
  have hpush' : IsPushout
      (G.left.obj.map (horiz hij hjk))
      (G.hom.hom.app (interval i j hij))
      (inv (e.hom.left.hom.app (interval i k (hij.trans hjk))) ≫ inl)
      (inv (e.hom.right.hom.app (interval i j hij)) ≫ inr) := by
    apply hpush.of_iso
      (asIso (e.hom.left.hom.app (interval i j hij)))
      (asIso (e.hom.left.hom.app (interval i k (hij.trans hjk))))
      (asIso (e.hom.right.hom.app (interval i j hij)))
      (Iso.refl P)
    · exact e.hom.left.hom.naturality (horiz hij hjk)
    · exact hsquare (interval i j hij)
    · simp
    · simp
  have hd' : IsCofibration
      (d ≫ e.hom.right.hom.app (interval i k (hij.trans hjk))) :=
    MorphismProperty.RespectsIso.postcomp
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C))
      (e.hom.right.hom.app (interval i k (hij.trans hjk))) d hd
  have hinl' :
      (inv (e.hom.left.hom.app (interval i k (hij.trans hjk))) ≫ inl) ≫
          (d ≫ e.hom.right.hom.app (interval i k (hij.trans hjk))) =
        G.hom.hom.app (interval i k (hij.trans hjk)) := by
    calc
      (inv (e.hom.left.hom.app (interval i k (hij.trans hjk))) ≫ inl) ≫
          (d ≫ e.hom.right.hom.app (interval i k (hij.trans hjk))) =
        inv (e.hom.left.hom.app (interval i k (hij.trans hjk))) ≫
          ((inl ≫ d) ≫
            e.hom.right.hom.app (interval i k (hij.trans hjk))) := by
              simp only [Category.assoc]
      _ = inv (e.hom.left.hom.app (interval i k (hij.trans hjk))) ≫
          (F.hom.hom.app (interval i k (hij.trans hjk)) ≫
            e.hom.right.hom.app (interval i k (hij.trans hjk))) := by rw [hinl]
      _ = inv (e.hom.left.hom.app (interval i k (hij.trans hjk))) ≫
          (e.hom.left.hom.app (interval i k (hij.trans hjk)) ≫
            G.hom.hom.app (interval i k (hij.trans hjk))) := by
              rw [hsquare]
      _ = G.hom.hom.app (interval i k (hij.trans hjk)) := by simp
  have hinr' :
      (inv (e.hom.right.hom.app (interval i j hij)) ≫ inr) ≫
          (d ≫ e.hom.right.hom.app (interval i k (hij.trans hjk))) =
        G.right.obj.map (horiz hij hjk) := by
    calc
      (inv (e.hom.right.hom.app (interval i j hij)) ≫ inr) ≫
          (d ≫ e.hom.right.hom.app (interval i k (hij.trans hjk))) =
        inv (e.hom.right.hom.app (interval i j hij)) ≫
          ((inr ≫ d) ≫
            e.hom.right.hom.app (interval i k (hij.trans hjk))) := by
              simp only [Category.assoc]
      _ = inv (e.hom.right.hom.app (interval i j hij)) ≫
          (F.right.obj.map (horiz hij hjk) ≫
            e.hom.right.hom.app (interval i k (hij.trans hjk))) := by rw [hinr]
      _ = inv (e.hom.right.hom.app (interval i j hij)) ≫
          (e.hom.right.hom.app (interval i j hij) ≫
            G.right.obj.map (horiz hij hjk)) := by
              rw [e.hom.right.hom.naturality]
      _ = G.right.obj.map (horiz hij hjk) := by simp
  exact ⟨P,
    inv (e.hom.left.hom.app (interval i k (hij.trans hjk))) ≫ inl,
    inv (e.hom.right.hom.app (interval i j hij)) ≫ inr,
    d ≫ e.hom.right.hom.app (interval i k (hij.trans hjk)),
    hpush', hinl', hinr', hd'⟩

instance stageCofibrations_respectsIso (n : ℕ) :
    (stageCofibrations C n).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso
    (stageCofibrations C n) (stageCofibrations_of_arrowIso C)

/-- Stage cofibrations are closed under composition. -/
theorem stageCofibrations_comp
    {n : ℕ} {A B D : Stage C n} (f : A ⟶ B) (g : B ⟶ D)
    (hf : stageCofibrations C n f) (hg : stageCofibrations C n g) :
    stageCofibrations C n (f ≫ g) := by
  apply stageCofibrations_of_everywhere C
  have hfevery : stageCofibrationsEverywhere C n f :=
    stageCofibrationsEverywhere_of_stageCofibrations C hf
  have hgevery : stageCofibrationsEverywhere C n g :=
    stageCofibrationsEverywhere_of_stageCofibrations C hg
  intro i j k hij hjk
  exact IsStageCofibrationCell.comp C f g hij hjk
    (hfevery hij hjk) (hgevery hij hjk)

instance stageCofibrations_isMultiplicative (n : ℕ) :
    (stageCofibrations C n).IsMultiplicative where
  id_mem := stageCofibrations_id C
  comp_mem := stageCofibrations_comp C

/-- Arbitrary simplex reindexing preserves the original successor-only stage
cofibration predicate. -/
theorem stageCofibrations_of_reindexStage
    {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B)
    (hf : stageCofibrations C b.len f) :
    stageCofibrations C a.len ((reindexStage α).map f) :=
  stageCofibrations_of_everywhere C
    (stageCofibrationsEverywhere_of_reindexStage C α f
      (stageCofibrationsEverywhere_of_stageCofibrations C hf))

end CategoryTheory.Waldhausen.SConstruction
