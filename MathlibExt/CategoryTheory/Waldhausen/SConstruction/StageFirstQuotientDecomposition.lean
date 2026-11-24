/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWaldhausenExact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageReindexWaldhausenExact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenGluing
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageEvaluationExactGeneral
public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductExact
public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductUnits
public import MathlibExt.CategoryTheory.Waldhausen.CoproductExactFunctorIso
public import MathlibExt.CategoryTheory.Waldhausen.ProductExactFunctor
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The original first-entry and first-face stage decomposition

The original first interval and the original zeroth face give the two
projection functors. The first-step insertion and first degeneracy retain
their actual interval data. The source cofibration sequence compares the
first-step part, the unchanged stage, and the degenerate quotient.

All diagonal zeros are retained as their original objects and compared
through zero isomorphisms. This is the source input to additivity; no
unlooped fiber or positive delooping statement is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

universe u v

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace StageFirstQuotient

/-- The first positive original vertex in degree `n+1`. -/
def firstIndex (n : ℕ) : Fin (n + 2) := (0 : Fin (n + 1)).succ

/-- This vertex is the original index one. -/
theorem firstIndex_eq_one (n : ℕ) : firstIndex n = (1 : Fin (n + 2)) := by
  apply Fin.ext
  change 1 = 1 % (n + 2)
  exact (Nat.mod_eq_of_lt (by omega : 1 < n + 2)).symm

/-- The original first-step interval simplex: zero followed by constant one. -/
def firstCut (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => if i = 0 then 0 else 1
      monotone' := by
        intro i j hij
        by_cases hj : j = 0
        · have hi : i = 0 := le_antisymm (hj ▸ hij) (Fin.zero_le i)
          simpa only [hi, hj, ite_true] using (le_refl (0 : Fin 2))
        · by_cases hi : i = 0
          · simp only [hi, ite_true, ite_eq_right hj]
            exact Fin.zero_le _
          · simp only [ite_eq_right hi, ite_eq_right hj]
            exact le_refl _ }

/-- The original first two vertices as an actual simplex inclusion. -/
def firstTwo (n : ℕ) : ⦋1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.mkOfLe 0 (firstIndex n) (Fin.zero_le _)

/-- The original first clamp, retaining zero and the first positive vertex. -/
def firstClamp (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋n + 1⦌ := firstCut n ≫ firstTwo n

/-- Every actual original index has the first-clamp value. -/
theorem firstClamp_apply (n : ℕ) (i : Fin (n + 2)) :
    (firstClamp n).toOrderHom i = if i = 0 then 0 else firstIndex n := by
  by_cases hi : i = 0
  · simp [firstClamp, firstCut, firstTwo, SimplexCategory.mkOfLe, SimplexCategory.mkHom, hi]
    rfl
  · simp [firstClamp, firstCut, firstTwo, SimplexCategory.mkOfLe, SimplexCategory.mkHom, hi]
    rfl

/-- The actual first degeneracy followed by the actual zeroth face. -/
def firstRaise (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.σ (0 : Fin (n + 1)) ≫ SimplexCategory.δ (0 : Fin (n + 2))

/-- The original composite only raises the zero vertex to the first positive vertex. -/
theorem firstRaise_apply (n : ℕ) (i : Fin (n + 2)) :
    (firstRaise n).toOrderHom i = if i = 0 then firstIndex n else i := by
  change (0 : Fin (n + 2)).succAbove ((0 : Fin (n + 1)).predAbove i) = _
  rw [Fin.succAbove_zero_apply]
  by_cases hi : i = 0
  · simp only [hi, Fin.predAbove_right_zero, firstIndex, ite_true]
  · rw [ite_eq_right hi]
    exact Fin.succ_predAbove_zero hi

/-- The original constant-one simplex operator. -/
def firstConstant (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.const _ _ (firstIndex n)

/-- Every positive original index is at least the first positive vertex. -/
theorem firstIndex_le (n : ℕ) {i : Fin (n + 2)} (hi : i ≠ 0) : firstIndex n ≤ i := by
  rw [Fin.le_iff_val_le_val]
  change 1 ≤ i.val
  have hpos : i.val ≠ 0 := fun h => hi (Fin.ext h)
  omega

/-- The original first clamp lies below the original identity operator. -/
theorem firstClamp_le_identity (n : ℕ) (i : Fin (n + 2)) :
    (firstClamp n).toOrderHom i ≤ (𝟙 ⦋n + 1⦌).toOrderHom i := by
  rw [firstClamp_apply]
  by_cases hi : i = 0
  · simp only [ite_eq_left hi]
    exact Fin.zero_le _
  · simp only [ite_eq_right hi]
    exact firstIndex_le n hi

/-- The original identity operator lies below the original first raise. -/
theorem identity_le_firstRaise (n : ℕ) (i : Fin (n + 2)) :
    (𝟙 ⦋n + 1⦌).toOrderHom i ≤ (firstRaise n).toOrderHom i := by
  rw [firstRaise_apply]
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    exact Fin.zero_le _
  · simp only [ite_eq_right hi]
    exact le_refl _

/-- The actual first clamp lies below the actual constant-one operator. -/
theorem firstClamp_le_constant (n : ℕ) (i : Fin (n + 2)) :
    (firstClamp n).toOrderHom i ≤ (firstConstant n).toOrderHom i := by
  rw [firstClamp_apply]
  change (if i = 0 then 0 else firstIndex n) ≤ firstIndex n
  split_ifs
  · exact Fin.zero_le _
  · exact le_refl _

/-- The actual constant-one operator lies below the actual first raise. -/
theorem constant_le_firstRaise (n : ℕ) (i : Fin (n + 2)) :
    (firstConstant n).toOrderHom i ≤ (firstRaise n).toOrderHom i := by
  rw [firstRaise_apply]
  change firstIndex n ≤ if i = 0 then firstIndex n else i
  by_cases hi : i = 0
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    exact firstIndex_le n hi

/-- The original first-entry evaluation through the actual first-two chart. -/
def source (n : ℕ) : Stage C (n + 1) ⥤ C :=
  reindexStage (C := C) (firstTwo n) ⋙ stageOneEval C

/-- The actual zeroth-face quotient of the original stage. -/
def quotient (n : ℕ) : Stage C (n + 1) ⥤ Stage C n :=
  reindexStage (C := C) (SimplexCategory.δ (0 : Fin (n + 2)))

/-- The original first-step insertion with its original chosen zero diagrams. -/
def insert (n : ℕ) : C ⥤ Stage C (n + 1) :=
  stageOne C ⋙ reindexStage (C := C) (firstCut n)

/-- The actual first degeneracy returns the quotient to the original stage category. -/
def degenerateReturn (n : ℕ) : Stage C n ⥤ Stage C (n + 1) :=
  reindexStage (C := C) (SimplexCategory.σ (0 : Fin (n + 1)))

/-- The entire original first-entry/quotient projection. -/
def projection (n : ℕ) : Stage C (n + 1) ⥤ C × Stage C n :=
  (source C n).prod' (quotient C n)

/-- The actual first-step endofunctor used by the source decomposition. -/
def firstEndo (n : ℕ) : Stage C (n + 1) ⥤ Stage C (n + 1) :=
  source C n ⋙ insert C n

/-- The literal clamp preserves every original diagonal zero object. -/
def firstClampEndo (n : ℕ) : Stage C (n + 1) ⥤ Stage C (n + 1) :=
  reindexStage (C := C) (firstClamp n)

/-- The actual quotient followed by the actual first degeneracy. -/
def quotientEndo (n : ℕ) : Stage C (n + 1) ⥤ Stage C (n + 1) :=
  quotient C n ⋙ degenerateReturn C n

/-- The actual constant stage at the original diagonal value `A11`. -/
def zeroEndo (n : ℕ) : Stage C (n + 1) ⥤ Stage C (n + 1) :=
  reindexStage (C := C) (firstConstant n)

/-- The original S1 counit compares the chosen-zero first insertion with
the literal first clamp, retaining all original zero isomorphisms. -/
def firstEndoIso (n : ℕ) : firstEndo C n ≅ firstClampEndo C n :=
  Functor.isoWhiskerLeft (reindexStage (C := C) (firstTwo n))
    (Functor.isoWhiskerRight (stageOneEvalCounit C) (reindexStage (C := C) (firstCut n)))

/-- The literal first clamp maps to the unchanged original stage. -/
def clampInclusion (n : ℕ) : firstClampEndo C n ⟶ 𝟭 (Stage C (n + 1)) :=
  reindexStageNatTransOfLE C (firstClamp n) (𝟙 _) (firstClamp_le_identity n)

/-- The original first-step inclusion retains its actual counit and interval map. -/
def sourceInclusion (n : ℕ) : firstEndo C n ⟶ 𝟭 (Stage C (n + 1)) :=
  (firstEndoIso C n).hom ≫ clampInclusion C n

/-- The unchanged original stage maps to its actual degenerate quotient. -/
def quotientProjection (n : ℕ) : 𝟭 (Stage C (n + 1)) ⟶ quotientEndo C n :=
  reindexStageNatTransOfLE C (𝟙 _) (firstRaise n) (identity_le_firstRaise n)

/-- The literal clamp maps to the actual constant `A11` stage. -/
def clampToZero (n : ℕ) : firstClampEndo C n ⟶ zeroEndo C n :=
  reindexStageNatTransOfLE C (firstClamp n) (firstConstant n) (firstClamp_le_constant n)

/-- The actual constant `A11` stage maps to the actual degenerate quotient. -/
def zeroToQuotient (n : ℕ) : zeroEndo C n ⟶ quotientEndo C n :=
  reindexStageNatTransOfLE C (firstConstant n) (firstRaise n) (constant_le_firstRaise n)

/-- The whole first-entry value is the actual original `A01`. -/
theorem source_obj (n : ℕ) (A : Stage C (n + 1)) :
    (source C n).obj A = A.obj.obj (interval 0 (firstIndex n) (Fin.zero_le _)) := by
  change A.obj.obj ((indexFunctor (firstTwo n)).obj
    (interval (0 : Fin 2) 1 (by decide))) = _
  rw [indexFunctor_obj_interval]
  rfl

/-- The full first-entry morphism is the same original interval component. -/
theorem source_map (n : ℕ) {A B : Stage C (n + 1)} (φ : A ⟶ B) :
    HEq ((source C n).map φ) (φ.hom.app (interval 0 (firstIndex n) (Fin.zero_le _))) := by
  change HEq (φ.hom.app ((indexFunctor (firstTwo n)).obj
    (interval (0 : Fin 2) 1 (by decide)))) _
  rw [indexFunctor_obj_interval]
  rfl

/-- The whole quotient interval diagram is the original zeroth-face pullback. -/
theorem quotient_obj (n : ℕ) (A : Stage C (n + 1)) :
    ((quotient C n).obj A).obj =
      indexFunctor (SimplexCategory.δ (0 : Fin (n + 2))) ⋙ A.obj := rfl

/-- Every quotient morphism is the actual original interval prewhiskering. -/
theorem quotient_map (n : ℕ) {A B : Stage C (n + 1)} (φ : A ⟶ B) :
    ((quotient C n).map φ).hom =
      Functor.whiskerLeft (indexFunctor (SimplexCategory.δ (0 : Fin (n + 2)))) φ.hom := rfl

/-- The whole inclusion is the original chosen-zero counit followed by the
literal ordinal first-clamp map. -/
theorem sourceInclusion_app (n : ℕ) (A : Stage C (n + 1)) :
    (sourceInclusion C n).app A =
      (firstEndoIso C n).hom.app A ≫ (clampInclusion C n).app A := rfl

/-- Every quotient component is the actual original index-comparison morphism. -/
theorem quotientProjection_app (n : ℕ) (A : Stage C (n + 1)) (x : Ar (n + 1)) :
    ((quotientProjection C n).app A).hom.app x =
      A.obj.map ((indexFunctorNatTransOfLE (𝟙 ⦋n + 1⦌) (firstRaise n)
        (identity_le_firstRaise n)).app x) := rfl

private theorem indexObject_eq {a b : SimplexCategory} (f : a ⟶ b)
    (x : Ar a.len) (y : Ar b.len)
    (h₀ : f.toOrderHom x.left = y.left) (h₁ : f.toOrderHom x.right = y.right) :
    (indexFunctor f).obj x = y :=
  Arrow.ext h₀ h₁ (Subsingleton.elim _ _)

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
private theorem isPushout_of_vertical_isos {Z X Y P : C}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (hg : IsIso g) (hl : IsIso inl) (w : f ≫ inl = g ≫ inr) :
    IsPushout f g inl inr :=
  @IsPushout.of_vert_isIso C _ Z X Y P f g inl inr hg hl ⟨w⟩

/-- Every later first-step zero-row map is an isomorphism of the actual
original coefficient object. -/
theorem firstEndo_tail_isIso (n : ℕ) (A : Stage C (n + 1))
    (i : Fin (n + 1)) (hi : i ≠ 0) :
    IsIso (((firstEndo C n).obj A).zeroRowSuccMap i) := by
  let Y := (stageOne C).obj ((source C n).obj A)
  let x : Ar (n + 1) := interval 0 i.castSucc (Fin.zero_le _)
  let y : Ar (n + 1) := interval 0 i.succ (Fin.zero_le _)
  let f : x ⟶ y := horiz (Fin.zero_le i.castSucc) i.castSucc_le_succ
  have hCast : i.castSucc ≠ (0 : Fin (n + 2)) := by
    intro h
    apply hi
    exact Fin.ext (congrArg (fun j : Fin (n + 2) => j.val) h)
  have hSucc : i.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
  have hCut0 : (firstCut n).toOrderHom (0 : Fin (n + 2)) = 0 := rfl
  have hCutCast : (firstCut n).toOrderHom i.castSucc = 1 := by
    change (if i.castSucc = 0 then 0 else 1) = 1
    rw [ite_eq_right hCast]
  have hCutSucc : (firstCut n).toOrderHom i.succ = 1 := by
    change (if i.succ = 0 then 0 else 1) = 1
    rw [ite_eq_right hSucc]
  have hxy : (indexFunctor (firstCut n)).obj x = (indexFunctor (firstCut n)).obj y := by
    let z : Ar 1 := interval (0 : Fin 2) 1 (by decide)
    exact (indexObject_eq (firstCut n) x z hCut0 hCutCast).trans
      (indexObject_eq (firstCut n) y z hCut0 hCutSucc).symm
  have hf : (indexFunctor (firstCut n)).map f = eqToHom hxy := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  let _ : IsIso ((indexFunctor (firstCut n)).map f) := by
    rw [hf]
    exact (eqToIso hxy).isIso_hom
  change IsIso (Y.obj.map ((indexFunctor (firstCut n)).map f))
  infer_instance

/-- The literal clamp inclusion is an isomorphism on the entire original first interval. -/
theorem clampInclusion_first_isIso (n : ℕ) (A : Stage C (n + 1)) :
    IsIso (((clampInclusion C n).app A).hom.app
      (interval 0 (firstIndex n) (Fin.zero_le _))) := by
  let x : Ar (n + 1) := interval 0 (firstIndex n) (Fin.zero_le _)
  let h := firstClamp_le_identity n
  have hx : (indexFunctor (firstClamp n)).obj x = x := by
    dsimp only [x]
    rw [indexFunctor_obj_interval]
    simp only [firstClamp_apply, ite_true,
      ite_eq_right (Fin.succ_ne_zero (0 : Fin (n + 1))), firstIndex]
  have hf : (indexFunctorNatTransOfLE (firstClamp n) (𝟙 _) h).app x = eqToHom hx := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  let _ : IsIso ((indexFunctorNatTransOfLE (firstClamp n) (𝟙 _) h).app x) := by
    rw [hf]
    exact (eqToIso hx).isIso_hom
  change IsIso (A.obj.map ((indexFunctorNatTransOfLE (firstClamp n) (𝟙 _) h).app x))
  infer_instance

/-- The chosen-zero first inclusion is an isomorphism on the original first
interval, through its actual S1 counit. -/
theorem sourceInclusion_first_isIso (n : ℕ) (A : Stage C (n + 1)) :
    IsIso (((sourceInclusion C n).app A).hom.app
      (interval 0 (firstIndex n) (Fin.zero_le _))) := by
  let x : Ar (n + 1) := interval 0 (firstIndex n) (Fin.zero_le _)
  let e := (firstEndoIso C n).app A
  let _ : IsIso (e.hom.hom.app x) := ((eval C (n + 1) x).mapIso e).isIso_hom
  let _ : IsIso (((clampInclusion C n).app A).hom.app x) :=
    clampInclusion_first_isIso C n A
  change IsIso (e.hom.hom.app x ≫ ((clampInclusion C n).app A).hom.app x)
  infer_instance

private theorem stageCofibrations_of_firstIso_tailIso (n : ℕ)
    {A B : Stage C (n + 1)} (f : A ⟶ B)
    (hFirst : IsIso (Stage.zeroRowApp f (firstIndex n)))
    (hTail : ∀ i : Fin (n + 1), i ≠ 0 → IsIso (A.zeroRowSuccMap i)) :
    stageCofibrations C (n + 1) f := by
  intro i
  have hNat : A.zeroRowSuccMap i ≫ Stage.zeroRowApp f i.succ =
      Stage.zeroRowApp f i.castSucc ≫ B.zeroRowSuccMap i :=
    f.hom.naturality (horiz (Fin.zero_le i.castSucc) i.castSucc_le_succ)
  by_cases hi : i = 0
  · subst i
    let hZero : IsIso (Stage.zeroRowApp f (0 : Fin (n + 1)).castSucc) := by
      rw [Fin.castSucc_zero]
      exact IsZero.isIso (A.property.diag_isZero 0) (B.property.diag_isZero 0) _
    let : IsIso (Stage.zeroRowApp f (firstIndex n)) := hFirst
    refine ⟨B.zeroRowObj (firstIndex n), Stage.zeroRowApp f (firstIndex n),
      B.zeroRowSuccMap 0, 𝟙 _, ?_, Category.comp_id _, Category.comp_id _, ?_⟩
    · exact isPushout_of_vertical_isos C hZero hFirst hNat
    · exact WaldhausenCategoryWithoutGluing.cofibrations.id_mem _
  · let a := A.zeroRowSuccMap i
    let b := B.zeroRowSuccMap i
    let f₀ := Stage.zeroRowApp f i.castSucc
    let f₁ := Stage.zeroRowApp f i.succ
    let _ : IsIso a := hTail i hi
    refine ⟨B.zeroRowObj i.castSucc, inv a ≫ f₀, 𝟙 _, b, ?_, ?_, Category.id_comp _, ?_⟩
    · exact IsPushout.of_horiz_isIso ⟨by
        change a ≫ (inv a ≫ f₀) = f₀ ≫ 𝟙 _
        simp only [IsIso.hom_inv_id_assoc, Category.comp_id]⟩
    · change (inv a ≫ f₀) ≫ b = f₁
      rw [Category.assoc, ← hNat, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    · exact (B.property.cofiber_triple (Fin.zero_le i.castSucc) i.castSucc_le_succ).1

/-- The actual first-step inclusion is a genuine successive-corner stage cofibration. -/
theorem sourceInclusion_isStageCofibration (n : ℕ) (A : Stage C (n + 1)) :
    stageCofibrations C (n + 1) ((sourceInclusion C n).app A) :=
  stageCofibrations_of_firstIso_tailIso C n ((sourceInclusion C n).app A)
    (sourceInclusion_first_isIso C n A) (firstEndo_tail_isIso C n A)

private theorem prefixPushout_corner_isStageCofibration (n : ℕ)
    {LA LB A B Q : Stage C (n + 1)}
    (ηA : LA ⟶ A) (ηB : LB ⟶ B) (v : LA ⟶ LB) (φ : A ⟶ B)
    (a : A ⟶ Q) (b : LB ⟶ Q) (d : Q ⟶ B)
    (hP : ∀ x : Ar (n + 1),
      IsPushout (ηA.hom.app x) (v.hom.app x) (a.hom.app x) (b.hom.app x))
    (ha : a ≫ d = φ) (hb : b ≫ d = ηB)
    (hφ : stageCofibrations C (n + 1) φ)
    (hA : IsIso (Stage.zeroRowApp ηA (firstIndex n)))
    (hB : IsIso (Stage.zeroRowApp ηB (firstIndex n)))
    (hLA : ∀ i : Fin (n + 1), i ≠ 0 → IsIso (LA.zeroRowSuccMap i))
    (hLB : ∀ i : Fin (n + 1), i ≠ 0 → IsIso (LB.zeroRowSuccMap i)) :
    stageCofibrations C (n + 1) d := by
  have ha₀ (j : Fin (n + 2)) :
      Stage.zeroRowApp a j ≫ Stage.zeroRowApp d j = Stage.zeroRowApp φ j :=
    congrArg (fun f => f.hom.app (interval 0 j (Fin.zero_le _))) ha
  have hb₀ (j : Fin (n + 2)) :
      Stage.zeroRowApp b j ≫ Stage.zeroRowApp d j = Stage.zeroRowApp ηB j :=
    congrArg (fun f => f.hom.app (interval 0 j (Fin.zero_le _))) hb
  intro i
  by_cases hi : i = 0
  · subst i
    let ηA₁ := Stage.zeroRowApp ηA (firstIndex n)
    let ηB₁ := Stage.zeroRowApp ηB (firstIndex n)
    let b₁ := Stage.zeroRowApp b (firstIndex n)
    let d₁ := Stage.zeroRowApp d (firstIndex n)
    let : IsIso ηA₁ := hA
    let : IsIso ηB₁ := hB
    let : IsIso (ηA.hom.app (interval 0 (firstIndex n) (Fin.zero_le _))) := by
      change IsIso (Stage.zeroRowApp ηA (firstIndex n))
      exact hA
    let : IsIso b₁ :=
      (hP (interval 0 (firstIndex n) (Fin.zero_le _))).isIso_inr_of_isIso hA
    have hd₁ : d₁ = inv b₁ ≫ ηB₁ := by
      have h : b₁ ≫ d₁ = ηB₁ := hb₀ (firstIndex n)
      rw [← h, IsIso.inv_hom_id_assoc]
    let hD : IsIso d₁ := hd₁ ▸ inferInstance
    let hZero : IsIso (Stage.zeroRowApp d (0 : Fin (n + 1)).castSucc) := by
      rw [Fin.castSucc_zero]
      exact IsZero.isIso (Q.property.diag_isZero 0) (B.property.diag_isZero 0) _
    refine ⟨B.zeroRowObj (firstIndex n), d₁, B.zeroRowSuccMap 0, 𝟙 _, ?_,
      Category.comp_id _, Category.comp_id _, WaldhausenCategoryWithoutGluing.cofibrations.id_mem _⟩
    exact isPushout_of_vertical_isos C hZero hD
      (d.hom.naturality (horiz (Fin.zero_le (0 : Fin (n + 1)).castSucc)
        (0 : Fin (n + 1)).castSucc_le_succ))
  · let x : Ar (n + 1) := interval 0 i.castSucc (Fin.zero_le _)
    let y : Ar (n + 1) := interval 0 i.succ (Fin.zero_le _)
    let f : x ⟶ y := horiz (Fin.zero_le i.castSucc) i.castSucc_le_succ
    let lA := LA.zeroRowSuccMap i
    let lB := LB.zeroRowSuccMap i
    let aRow := A.zeroRowSuccMap i
    let qRow := Q.zeroRowSuccMap i
    let v₀ := Stage.zeroRowApp v i.castSucc
    let v₁ := Stage.zeroRowApp v i.succ
    let η₀ := Stage.zeroRowApp ηA i.castSucc
    let η₁ := Stage.zeroRowApp ηA i.succ
    let a₀ := Stage.zeroRowApp a i.castSucc
    let a₁ := Stage.zeroRowApp a i.succ
    let b₀ := Stage.zeroRowApp b i.castSucc
    let b₁ := Stage.zeroRowApp b i.succ
    let d₀ := Stage.zeroRowApp d i.castSucc
    let d₁ := Stage.zeroRowApp d i.succ
    let _ : IsIso lA := hLA i hi
    let _ : IsIso lB := hLB i hi
    have hIso : IsPushout lA v₀ v₁ lB :=
      IsPushout.of_horiz_isIso ⟨v.hom.naturality f⟩
    have hOuter : IsPushout (η₀ ≫ aRow) v₀ a₁ (b₀ ≫ qRow) := by
      have h := hIso.paste_horiz (hP y)
      change IsPushout (LA.obj.map f ≫ ηA.hom.app y) (v.hom.app x)
        (a.hom.app y) (LB.obj.map f ≫ b.hom.app y) at h
      rw [ηA.hom.naturality f, b.hom.naturality f] at h
      exact h
    have hStep : IsPushout aRow a₀ a₁ qRow :=
      hOuter.of_left (a.hom.naturality f) (hP x)
    obtain ⟨T, inA, inB, c, hT, hA, hB, hc⟩ := hφ i
    have hw : aRow ≫ inA = a₀ ≫ (d₀ ≫ inB) := by
      calc
        aRow ≫ inA = Stage.zeroRowApp φ i.castSucc ≫ inB := hT.w
        _ = (a₀ ≫ d₀) ≫ inB := congrArg (· ≫ inB) (ha₀ i.castSucc).symm
        _ = a₀ ≫ (d₀ ≫ inB) := Category.assoc _ _ _
    let u : Q.zeroRowObj i.succ ⟶ T := hStep.desc inA (d₀ ≫ inB) hw
    have huA : a₁ ≫ u = inA := hStep.inl_desc _ _ _
    have huQ : qRow ≫ u = d₀ ≫ inB := hStep.inr_desc _ _ _
    have hOriginal : IsPushout aRow (a₀ ≫ d₀) (a₁ ≫ u) inB := by
      rw [ha₀ i.castSucc, huA]
      exact hT
    have hCorner : IsPushout qRow d₀ u inB := hOriginal.of_top huQ hStep
    refine ⟨T, u, inB, c, hCorner, ?_, hB, hc⟩
    apply hStep.hom_ext
    · rw [← Category.assoc, huA, hA, ha₀ i.succ]
    · rw [← Category.assoc, huQ, Category.assoc, hB]
      exact (d.hom.naturality f).symm

/-- The actual stock pushout of the source first-step inclusion has a
genuine original relative stage corner on every source stage cofibration. -/
theorem sourceInclusion_baseCofibration (n : ℕ) {A B : Stage C (n + 1)}
    (φ : A ⟶ B) (hφ : stageCofibrations C (n + 1) φ) :
    letI : HasPushout ((sourceInclusion C n).app A) ((firstEndo C n).map φ) := by
      let P := GeneralStagePushoutPresentation.ofStageCofibration
        ((sourceInclusion C n).app A) ((firstEndo C n).map φ)
        (sourceInclusion_isStageCofibration C n A)
      exact P.isPushout.flip.hasPushout
    stageCofibrations C (n + 1)
      (pushout.desc φ ((sourceInclusion C n).app B)
        ((sourceInclusion C n).naturality φ).symm) := by
  let ηA := (sourceInclusion C n).app A
  let ηB := (sourceInclusion C n).app B
  let v := (firstEndo C n).map φ
  let _ : HasPushout ηA v := by
    let P := GeneralStagePushoutPresentation.ofStageCofibration ηA v
      (sourceInclusion_isStageCofibration C n A)
    exact P.isPushout.flip.hasPushout
  let Q := pushout ηA v
  let a : A ⟶ Q := pushout.inl ηA v
  let b : (firstEndo C n).obj B ⟶ Q := pushout.inr ηA v
  let d : Q ⟶ B := pushout.desc φ ηB ((sourceInclusion C n).naturality φ).symm
  have hP : ∀ x : Ar (n + 1),
      IsPushout (ηA.hom.app x) (v.hom.app x) (a.hom.app x) (b.hom.app x) := by
    intro x
    exact (GeneralStagePushoutPresentation.isPushout_app
      (sourceInclusion_isStageCofibration C n A)
      (IsPushout.of_hasPushout ηA v).flip x).flip
  exact prefixPushout_corner_isStageCofibration C n ηA ηB v φ a b d hP
    (pushout.inl_desc _ _ _) (pushout.inr_desc _ _ _) hφ
    (sourceInclusion_first_isIso C n A) (sourceInclusion_first_isIso C n B)
    (firstEndo_tail_isIso C n A) (firstEndo_tail_isIso C n B)

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
private theorem pushout_map_of_index_eq (n : ℕ) (A : Ar (n + 1) ⥤ C)
    {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Ar (n + 1)}
    (f : x₀ ⟶ x₁) (g : x₀ ⟶ x₂) (r : x₁ ⟶ x₃) (b : x₂ ⟶ x₃)
    (f' : y₀ ⟶ y₁) (g' : y₀ ⟶ y₂) (r' : y₁ ⟶ y₃) (b' : y₂ ⟶ y₃)
    (hP : IsPushout (A.map f) (A.map g) (A.map r) (A.map b))
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) (h₃ : x₃ = y₃) :
    IsPushout (A.map f') (A.map g') (A.map r') (A.map b') := by
  apply hP.of_iso (A.mapIso (eqToIso h₀)) (A.mapIso (eqToIso h₁))
    (A.mapIso (eqToIso h₂)) (A.mapIso (eqToIso h₃))
  all_goals
    change A.map _ ≫ A.map _ = A.map _ ≫ A.map _
    rw [← A.map_comp, ← A.map_comp]
    congr 1

private theorem clampSquare_isPushout_app (n : ℕ) (A : Stage C (n + 1)) (x : Ar (n + 1)) :
    IsPushout (((clampInclusion C n).app A).hom.app x)
      (((clampToZero C n).app A).hom.app x)
      (((quotientProjection C n).app A).hom.app x)
      (((zeroToQuotient C n).app A).hom.app x) := by
  change IsPushout
    (A.obj.map ((indexFunctorNatTransOfLE (firstClamp n) (𝟙 _)
      (firstClamp_le_identity n)).app x))
    (A.obj.map ((indexFunctorNatTransOfLE (firstClamp n) (firstConstant n)
      (firstClamp_le_constant n)).app x))
    (A.obj.map ((indexFunctorNatTransOfLE (𝟙 _) (firstRaise n)
      (identity_le_firstRaise n)).app x))
    (A.obj.map ((indexFunctorNatTransOfLE (firstConstant n) (firstRaise n)
      (constant_le_firstRaise n)).app x))
  obtain ⟨i, j, f, rfl⟩ := Arrow.mk_surjective x
  let hij : i ≤ j := leOfHom f
  have hf : f = homOfLE hij := Subsingleton.elim _ _
  rw [hf]
  let x : Ar (n + 1) := interval i j hij
  let f' := (indexFunctorNatTransOfLE (firstClamp n) (𝟙 _)
    (firstClamp_le_identity n)).app x
  let g' := (indexFunctorNatTransOfLE (firstClamp n) (firstConstant n)
    (firstClamp_le_constant n)).app x
  let r' := (indexFunctorNatTransOfLE (𝟙 _) (firstRaise n)
    (identity_le_firstRaise n)).app x
  let b' := (indexFunctorNatTransOfLE (firstConstant n) (firstRaise n)
    (constant_le_firstRaise n)).app x
  change IsPushout (A.obj.map f') (A.obj.map g') (A.obj.map r') (A.obj.map b')
  have hz : (indexFunctor (firstConstant n)).obj x = diag (firstIndex n) := by
    rw [indexFunctor_obj_interval]
    rfl
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      let u : diag (0 : Fin (n + 2)) ⟶ diag (firstIndex n) :=
        Arrow.homMk' (homOfLE (Fin.zero_le _)) (homOfLE (Fin.zero_le _))
          (Subsingleton.elim _ _)
      have hk : (indexFunctor (firstClamp n)).obj x = diag (0 : Fin (n + 2)) := by
        exact indexObject_eq (firstClamp n) x (diag (0 : Fin (n + 2)))
          (by
            change (firstClamp n).toOrderHom (0 : Fin (n + 2)) = 0
            simpa using firstClamp_apply n (0 : Fin (n + 2)))
          (by
            change (firstClamp n).toOrderHom (0 : Fin (n + 2)) = 0
            simpa using firstClamp_apply n (0 : Fin (n + 2)))
      have hg : (indexFunctor (firstRaise n)).obj x = diag (firstIndex n) := by
        exact indexObject_eq (firstRaise n) x (diag (firstIndex n))
          (by
            change (firstRaise n).toOrderHom (0 : Fin (n + 2)) = firstIndex n
            simpa using firstRaise_apply n (0 : Fin (n + 2)))
          (by
            change (firstRaise n).toOrderHom (0 : Fin (n + 2)) = firstIndex n
            simpa using firstRaise_apply n (0 : Fin (n + 2)))
      have hP : IsPushout (A.obj.map (𝟙 (diag (0 : Fin (n + 2)))))
          (A.obj.map u) (A.obj.map u) (A.obj.map (𝟙 (diag (firstIndex n)))) := by
        simpa only [Functor.map_id] using (IsPushout.of_id_fst (f := A.obj.map u))
      exact pushout_map_of_index_eq C n A.obj _ u u _ f' g' r' b' hP
        hk.symm rfl hz.symm hg.symm
    · have h1j : firstIndex n ≤ j := firstIndex_le n hj
      have hk : (indexFunctor (firstClamp n)).obj x =
          interval 0 (firstIndex n) (Fin.zero_le _) := by
        exact indexObject_eq (firstClamp n) x (interval 0 (firstIndex n) (Fin.zero_le _))
          (by
            change (firstClamp n).toOrderHom (0 : Fin (n + 2)) = 0
            simpa using firstClamp_apply n (0 : Fin (n + 2)))
          (by
            change (firstClamp n).toOrderHom j = firstIndex n
            simpa only [ite_eq_right hj] using firstClamp_apply n j)
      have hg : (indexFunctor (firstRaise n)).obj x = interval (firstIndex n) j h1j := by
        exact indexObject_eq (firstRaise n) x (interval (firstIndex n) j h1j)
          (by
            change (firstRaise n).toOrderHom (0 : Fin (n + 2)) = firstIndex n
            simpa using firstRaise_apply n (0 : Fin (n + 2)))
          (by
            change (firstRaise n).toOrderHom j = j
            simpa only [ite_eq_right hj] using firstRaise_apply n j)
      exact pushout_map_of_index_eq C n A.obj
        (horiz (Fin.zero_le (firstIndex n)) h1j) (toDiag (Fin.zero_le (firstIndex n)))
        (vert (Fin.zero_le (firstIndex n)) h1j) (fromDiag h1j)
        f' g' r' b' (isPushout_actualSquare A.property (Fin.zero_le _) h1j)
        hk.symm rfl hz.symm hg.symm
  · have hj : j ≠ 0 := by
      intro h
      exact hi (le_antisymm (h ▸ hij) (Fin.zero_le i))
    let u : diag (firstIndex n) ⟶ x :=
      Arrow.homMk' (homOfLE (firstIndex_le n hi)) (homOfLE (firstIndex_le n hj))
        (Subsingleton.elim _ _)
    have hk : (indexFunctor (firstClamp n)).obj x = diag (firstIndex n) := by
      exact indexObject_eq (firstClamp n) x (diag (firstIndex n))
        (by
          change (firstClamp n).toOrderHom i = firstIndex n
          simpa only [ite_eq_right hi] using firstClamp_apply n i)
        (by
          change (firstClamp n).toOrderHom j = firstIndex n
          simpa only [ite_eq_right hj] using firstClamp_apply n j)
    have hg : (indexFunctor (firstRaise n)).obj x = x := by
      exact indexObject_eq (firstRaise n) x x
        (by
          change (firstRaise n).toOrderHom i = i
          simpa only [ite_eq_right hi] using firstRaise_apply n i)
        (by
          change (firstRaise n).toOrderHom j = j
          simpa only [ite_eq_right hj] using firstRaise_apply n j)
    have hP : IsPushout (A.obj.map u) (A.obj.map (𝟙 (diag (firstIndex n))))
        (A.obj.map (𝟙 x)) (A.obj.map u) := by
      simpa only [Functor.map_id] using (IsPushout.of_id_snd (f := A.obj.map u))
    exact pushout_map_of_index_eq C n A.obj u _ _ u f' g' r' b' hP
      hk.symm rfl hz.symm hg.symm

/-- The entire original clamp square is a stage pushout, with all actual
interval pushouts earned from the original cofiber triples. -/
theorem clampSquare_isPushout (n : ℕ) (A : Stage C (n + 1)) :
    IsPushout ((clampInclusion C n).app A) ((clampToZero C n).app A)
      ((quotientProjection C n).app A) ((zeroToQuotient C n).app A) := by
  apply IsPushout.of_map_of_faithful (forget C (n + 1))
  apply IsPushout.of_forall_isPushout_app
  intro x
  exact clampSquare_isPushout_app C n A x

/-- The actual constant stage at the original diagonal `A11` is zero,
without replacing that diagonal object by the chosen base zero. -/
theorem zeroEndo_isZero (n : ℕ) (A : Stage C (n + 1)) :
    IsZero ((zeroEndo C n).obj A) := by
  apply IsZero.of_full_of_faithful_of_isZero (forget C (n + 1))
  apply Functor.isZero
  intro x
  have hx : (indexFunctor (firstConstant n)).obj x = diag (firstIndex n) := by
    obtain ⟨i, j, f, rfl⟩ := Arrow.mk_surjective x
    rfl
  change IsZero (A.obj.obj ((indexFunctor (firstConstant n)).obj x))
  rw [hx]
  exact A.property.diag_isZero (firstIndex n)

/-- The original first-step inclusion and original quotient projection
form a cofiber sequence in the same named general stage category. -/
theorem objectwise_isCofiberSequence (n : ℕ) (A : Stage C (n + 1)) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    IsCofiberSequence ((sourceInclusion C n).app A) ((quotientProjection C n).app A) := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let eL := (firstEndoIso C n).app A
  let eZ := (zeroEndo_isZero C n A).isoZero
  let toZero : (firstEndo C n).obj A ⟶ (0 : Stage C (n + 1)) :=
    eL.hom ≫ (clampToZero C n).app A ≫ eZ.hom
  let fromZero : (0 : Stage C (n + 1)) ⟶ (quotientEndo C n).obj A :=
    eZ.inv ≫ (zeroToQuotient C n).app A
  have hP : IsPushout ((sourceInclusion C n).app A) toZero
      ((quotientProjection C n).app A) fromZero := by
    apply (clampSquare_isPushout C n A).of_iso eL.symm (Iso.refl _) eZ (Iso.refl _)
    · simp only [sourceInclusion_app, Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      change (clampInclusion C n).app A =
        eL.inv ≫ eL.hom ≫ (clampInclusion C n).app A
      simp only [Iso.inv_hom_id_assoc]
    · simp only [toZero, Iso.symm_hom]
      simp only [Iso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [fromZero, Iso.hom_inv_id_assoc, Iso.refl_hom,
        Category.comp_id]
  exact ⟨(isCofibration_generalStageWaldhausenCategory_iff C (n + 1) _).mpr
    (sourceInclusion_isStageCofibration C n A), toZero, fromZero, hP.flip⟩

/-- The source first-step endofunctor retains all four original exactness fields. -/
theorem firstEndo_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (firstEndo C n).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
  let _ : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
  exact ((reindexStage_general_isWaldhausenExact C (firstTwo n)).comp
    (stageOneEval_general_isWaldhausenExact C)).comp
      ((stageOne_general_isWaldhausenExact C).comp
        (reindexStage_general_isWaldhausenExact C (firstCut n)))

/-- The actual quotient-degeneracy endofunctor retains all original exactness fields. -/
theorem quotientEndo_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (quotientEndo C n).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let _ : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  exact (reindexStage_general_isWaldhausenExact C (SimplexCategory.δ (0 : Fin (n + 2)))).comp
    (reindexStage_general_isWaldhausenExact C (SimplexCategory.σ (0 : Fin (n + 1))))

/-- The actual first-entry/first-face decomposition satisfies Weibel's
source cofibration-sequence condition, including the internally earned base corner. -/
theorem isWaldhausenCofiberFunctorSequence (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    IsWaldhausenCofiberFunctorSequence (firstEndo C n) (𝟭 (Stage C (n + 1)))
      (quotientEndo C n) (sourceInclusion C n) (quotientProjection C n) := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  refine ⟨firstEndo_isWaldhausenExact C n, Functor.IsWaldhausenExact.id,
    quotientEndo_isWaldhausenExact C n, objectwise_isCofiberSequence C n, ?_⟩
  intro A B φ hφ
  apply (isCofibration_generalStageWaldhausenCategory_iff C (n + 1) _).mpr
  exact sourceInclusion_baseCofibration C n φ
    ((isCofibration_generalStageWaldhausenCategory_iff C (n + 1) φ).mp hφ)

/-- The stock original cofiber lift of the internally earned source sequence. -/
def cofiberLift (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    Stage C (n + 1) ⥤ CofiberSequenceCategory (Stage C (n + 1)) := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  exact cofiberFunctorSequenceLift (firstEndo C n) (𝟭 _) (quotientEndo C n)
    (sourceInclusion C n) (quotientProjection C n)
    (isWaldhausenCofiberFunctorSequence C n).objectwise

/-- The same stock lift is exact for the original relative cofiber Waldhausen value. -/
theorem cofiberLift_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C (n + 1))) :=
      CofiberSequenceCategory.relativeWaldhausenCategory (Stage C (n + 1))
    (cofiberLift C n).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C (n + 1))) :=
    CofiberSequenceCategory.relativeWaldhausenCategory (Stage C (n + 1))
  exact (isWaldhausenCofiberFunctorSequence C n).lift_isWaldhausenExact

/-- The original first-entry functor is exact for the named original stage value. -/
theorem source_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (source C n).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
  let _ : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
  exact (reindexStage_general_isWaldhausenExact C (firstTwo n)).comp
    (stageOneEval_general_isWaldhausenExact C)

/-- The original first-step insertion is exact for the named stage value. -/
theorem insert_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (insert C n).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
  let _ : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
  exact (stageOne_general_isWaldhausenExact C).comp
    (reindexStage_general_isWaldhausenExact C (firstCut n))

/-- The actual zeroth-face quotient is exact for the two original named stage values. -/
theorem quotient_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    (quotient C n).IsWaldhausenExact := by
  exact reindexStage_general_isWaldhausenExact C (SimplexCategory.δ (0 : Fin (n + 2)))

/-- The actual first degeneracy is exact for the two original named stage values. -/
theorem degenerateReturn_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (degenerateReturn C n).IsWaldhausenExact := by
  exact reindexStage_general_isWaldhausenExact C (SimplexCategory.σ (0 : Fin (n + 1)))

/-- The actual first two vertices followed by the original first cut retain the identity. -/
theorem firstTwo_comp_firstCut (n : ℕ) : firstTwo n ≫ firstCut n = 𝟙 ⦋1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  fin_cases i <;> simp [firstTwo, firstCut, SimplexCategory.mkOfLe,
    SimplexCategory.mkHom, firstIndex]

/-- The entire first insertion/evaluation composite retains the original S1 unit Iso. -/
def insertSourceIso (n : ℕ) : insert C n ⋙ source C n ≅ 𝟭 C := by
  have h : insert C n ⋙ source C n = stageOne C ⋙ stageOneEval C := by
    change stageOne C ⋙
      (reindexStage (C := C) (firstCut n) ⋙ reindexStage (C := C) (firstTwo n)) ⋙
        stageOneEval C = _
    rw [← reindexStage_comp, firstTwo_comp_firstCut, reindexStage_id, Functor.id_comp]
  exact eqToIso h ≪≫ (stageOneEvalUnit C).symm

/-- The original first degeneracy followed by the original zeroth face is
the literal identity on every complete quotient stage. -/
theorem degenerateReturn_quotient (n : ℕ) :
    degenerateReturn C n ⋙ quotient C n = 𝟭 (Stage C n) := by
  unfold degenerateReturn quotient
  rw [← reindexStage_comp]
  have h : SimplexCategory.δ (0 : Fin (n + 2)) ≫
      SimplexCategory.σ (0 : Fin (n + 1)) = 𝟙 ⦋n⦌ := by
    simpa only [Fin.castSucc_zero] using
      (SimplexCategory.δ_comp_σ_self (n := n) (i := (0 : Fin (n + 1))))
  rw [h, reindexStage_id]

/-- The returned quotient's first entry is the actual original diagonal `Q00`. -/
theorem degenerateReturn_source_obj (n : ℕ) (Q : Stage C n) :
    (degenerateReturn C n ⋙ source C n).obj Q = Q.obj.obj (diag (0 : Fin (n + 1))) := by
  change (source C n).obj ((degenerateReturn C n).obj Q) = _
  rw [source_obj]
  change Q.obj.obj ((indexFunctor (SimplexCategory.σ (0 : Fin (n + 1)))).obj
    (interval 0 (firstIndex n) (Fin.zero_le _))) = _
  have h₀ : (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom (0 : Fin (n + 2)) = 0 :=
    Fin.predAbove_right_zero (i := (0 : Fin (n + 1)))
  have h₁ : (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom (firstIndex n) = 0 := by
    change Fin.predAbove (0 : Fin (n + 1)) (0 : Fin (n + 1)).succ = 0
    exact Fin.predAbove_succ_self (0 : Fin (n + 1))
  exact congrArg Q.obj.obj
    (indexObject_eq (SimplexCategory.σ (0 : Fin (n + 1)))
      (interval 0 (firstIndex n) (Fin.zero_le _)) (diag (0 : Fin (n + 1))) h₀ h₁)

/-- The returned quotient's first entry is zero, retaining its original `Q00` object. -/
theorem degenerateReturn_source_isZero (n : ℕ) (Q : Stage C n) :
    IsZero ((degenerateReturn C n ⋙ source C n).obj Q) := by
  rw [degenerateReturn_source_obj]
  exact Q.property.diag_isZero 0

/-- The actual returned first-entry zero has its full natural zero Iso to the chosen base zero. -/
def degenerateReturnSourceZeroIso (n : ℕ) :
    degenerateReturn C n ⋙ source C n ≅ (Functor.const (Stage C n)).obj (0 : C) :=
  NatIso.ofComponents (fun Q => (degenerateReturn_source_isZero C n Q).isoZero)
    (by intro Q Q' φ; exact (degenerateReturn_source_isZero C n Q).eq_of_src _ _)

/-- The original first insertion has an actual zero zeroth-face quotient. -/
theorem insert_quotient_isZero (n : ℕ) (X : C) :
    IsZero ((insert C n ⋙ quotient C n).obj X) := by
  apply IsZero.of_full_of_faithful_of_isZero (forget C n)
  apply Functor.isZero
  intro x
  let y := (indexFunctor (firstCut n)).obj
    ((indexFunctor (SimplexCategory.δ (0 : Fin (n + 2)))).obj x)
  have hLeft : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom x.left ≠ 0 := by
    change (0 : Fin (n + 2)).succAbove x.left ≠ 0
    rw [Fin.succAbove_zero_apply]
    exact Fin.succ_ne_zero _
  have hRight : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom x.right ≠ 0 := by
    change (0 : Fin (n + 2)).succAbove x.right ≠ 0
    rw [Fin.succAbove_zero_apply]
    exact Fin.succ_ne_zero _
  have hy : y.left = y.right := by
    change (if (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom x.left = 0 then 0 else 1) =
      (if (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom x.right = 0 then 0 else 1)
    rw [ite_eq_right hLeft, ite_eq_right hRight]
  change IsZero (((stageOne C).obj X).obj.obj y)
  rw [stageOne_obj_eq_zero_of_diag C X hy]
  exact isZero_zero C

/-- The actual zero quotient of the first insertion has its natural Iso to
the chosen zero of the same original quotient stage category. -/
def insertQuotientZeroIso (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    insert C n ⋙ quotient C n ≅ (Functor.const C).obj (0 : Stage C n) := by
  let _ : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  exact NatIso.ofComponents (fun X => (insert_quotient_isZero C n X).isoZero)
    (by intro X Y f; exact (insert_quotient_isZero C n X).eq_of_src _ _)

/-- The actual original split return is the original stage coproduct of
the first-step insertion and the returned quotient. -/
def splitReturn (n : ℕ) : C × Stage C n ⥤ Stage C (n + 1) := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  exact (insert C n).prod (degenerateReturn C n) ⋙
    Waldhausen.waldhausenCoproductFunctor (Stage C (n + 1))

/-- Every whole split-return stage is the same original chosen stage coproduct. -/
theorem splitReturn_obj (n : ℕ) (X : C) (Q : Stage C n) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (splitReturn C n).obj (X, Q) =
      (Waldhausen.waldhausenCoproductFunctor (Stage C (n + 1))).obj
        ((insert C n).obj X, (degenerateReturn C n).obj Q) := by
  rfl

/-- Every whole split-return morphism is the original coproduct map of both original components. -/
theorem splitReturn_map (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {Q Q' : Stage C n} (g : Q ⟶ Q') :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (splitReturn C n).map (X := (X, Q)) (Y := (Y, Q')) (f, g) =
      (Waldhausen.waldhausenCoproductFunctor (Stage C (n + 1))).map
        (X := ((insert C n).obj X, (degenerateReturn C n).obj Q))
        (Y := ((insert C n).obj Y, (degenerateReturn C n).obj Q'))
        ((insert C n).map f, (degenerateReturn C n).map g) := by
  rfl

/-- Every original split-return interval has the actual base coproduct
comparison supplied by exact evaluation, with both original components retained. -/
def splitReturnIntervalIso (n : ℕ) (X : C) (Q : Stage C n) (x : Ar (n + 1)) :
    ((splitReturn C n).obj (X, Q)).obj.obj x ≅
      (Waldhausen.waldhausenCoproductFunctor C).obj
        (((insert C n).obj X).obj.obj x, ((degenerateReturn C n).obj Q).obj.obj x) := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  exact ((evalIsGeneralStageWaldhausenExact C (n + 1) x).waldhausenCoproductIso).app
    ((insert C n).obj X, (degenerateReturn C n).obj Q)

/-- The whole first projection of the split return has its original coproduct,
S1-unit and actual returned-zero comparison. -/
def splitReturnSourceIso (n : ℕ) :
    splitReturn C n ⋙ source C n ≅ CategoryTheory.Prod.fst C (Stage C n) := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let K := (insert C n).prod (degenerateReturn C n)
  let T : C × Stage C n ⥤ C × C :=
    (CategoryTheory.Prod.fst C (Stage C n)).prod'
      ((Functor.const (C × Stage C n)).obj (0 : C))
  let e₁ : splitReturn C n ⋙ source C n ≅
      ((insert C n ⋙ source C n).prod (degenerateReturn C n ⋙ source C n)) ⋙
        Waldhausen.waldhausenCoproductFunctor C :=
    Functor.isoWhiskerLeft K (source_isWaldhausenExact C n).waldhausenCoproductIso
  let ePair : (insert C n ⋙ source C n).prod
      (degenerateReturn C n ⋙ source C n) ≅ T :=
    NatIso.ofComponents (fun p =>
      Iso.prod ((insertSourceIso C n).app p.1)
        ((degenerateReturnSourceZeroIso C n).app p.2)) (by
          intro p q φ
          apply Prod.hom_ext
          · exact (insertSourceIso C n).hom.naturality φ.1
          · exact (degenerateReturnSourceZeroIso C n).hom.naturality φ.2)
  have hT : T = CategoryTheory.Prod.fst C (Stage C n) ⋙
      Waldhausen.waldhausenZeroRightPair C := by
    rw [Waldhausen.waldhausenZeroRightPair_eq]
    rfl
  let e₂ := Functor.isoWhiskerRight ePair (Waldhausen.waldhausenCoproductFunctor C)
  let e₃ : T ⋙ Waldhausen.waldhausenCoproductFunctor C ≅
      CategoryTheory.Prod.fst C (Stage C n) :=
    eqToIso (congrArg (· ⋙ Waldhausen.waldhausenCoproductFunctor C) hT) ≪≫
      Functor.isoWhiskerLeft (CategoryTheory.Prod.fst C (Stage C n))
        (Waldhausen.waldhausenCoproductRightUnitIso C)
  exact e₁ ≪≫ e₂ ≪≫ e₃

/-- The whole quotient of the split return has its actual coproduct,
returned-quotient identity and original zero-left unit comparison. -/
def splitReturnQuotientIso (n : ℕ) :
    splitReturn C n ⋙ quotient C n ≅ CategoryTheory.Prod.snd C (Stage C n) := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let _ : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let K := (insert C n).prod (degenerateReturn C n)
  let T : C × Stage C n ⥤ Stage C n × Stage C n :=
    ((Functor.const (C × Stage C n)).obj (0 : Stage C n)).prod'
      (CategoryTheory.Prod.snd C (Stage C n))
  let e₁ : splitReturn C n ⋙ quotient C n ≅
      ((insert C n ⋙ quotient C n).prod (degenerateReturn C n ⋙ quotient C n)) ⋙
        Waldhausen.waldhausenCoproductFunctor (Stage C n) :=
    Functor.isoWhiskerLeft K (quotient_isWaldhausenExact C n).waldhausenCoproductIso
  let eReturn : degenerateReturn C n ⋙ quotient C n ≅ 𝟭 (Stage C n) :=
    eqToIso (degenerateReturn_quotient C n)
  let ePair : (insert C n ⋙ quotient C n).prod
      (degenerateReturn C n ⋙ quotient C n) ≅ T :=
    NatIso.ofComponents (fun p =>
      Iso.prod ((insertQuotientZeroIso C n).app p.1) (eReturn.app p.2)) (by
        intro p q φ
        apply Prod.hom_ext
        · exact (insertQuotientZeroIso C n).hom.naturality φ.1
        · exact eReturn.hom.naturality φ.2)
  have hT : T = CategoryTheory.Prod.snd C (Stage C n) ⋙
      Waldhausen.waldhausenZeroLeftPair (Stage C n) := by
    rw [Waldhausen.waldhausenZeroLeftPair_eq]
    rfl
  let e₂ := Functor.isoWhiskerRight ePair
    (Waldhausen.waldhausenCoproductFunctor (Stage C n))
  let e₃ : T ⋙ Waldhausen.waldhausenCoproductFunctor (Stage C n) ≅
      CategoryTheory.Prod.snd C (Stage C n) :=
    eqToIso (congrArg (· ⋙ Waldhausen.waldhausenCoproductFunctor (Stage C n)) hT) ≪≫
      Functor.isoWhiskerLeft (CategoryTheory.Prod.snd C (Stage C n))
        (Waldhausen.waldhausenCoproductLeftUnitIso (Stage C n))
  exact e₁ ≪≫ e₂ ≪≫ e₃

/-- The actual split return followed by the original projection has its full
natural identity comparison. The opposite composite is not asserted to split extensions. -/
def splitReturnProjectionIso (n : ℕ) :
    splitReturn C n ⋙ projection C n ≅ 𝟭 (C × Stage C n) :=
  NatIso.ofComponents (fun p =>
    Iso.prod ((splitReturnSourceIso C n).app p) ((splitReturnQuotientIso C n).app p)) (by
      intro p q φ
      apply Prod.hom_ext
      · exact (splitReturnSourceIso C n).hom.naturality φ
      · exact (splitReturnQuotientIso C n).hom.naturality φ)

/-- The first insertion retains its actual coefficient on the entire original first interval. -/
theorem insert_first_obj (n : ℕ) (X : C) :
    ((insert C n).obj X).obj.obj (interval 0 (firstIndex n) (Fin.zero_le _)) = X := by
  change ((stageOne C).obj X).obj.obj ((indexFunctor (firstCut n)).obj
    (interval 0 (firstIndex n) (Fin.zero_le _))) = X
  have h₀ : (firstCut n).toOrderHom (0 : Fin (n + 2)) = 0 := rfl
  have h₁ : (firstCut n).toOrderHom (firstIndex n) = 1 := by
    change (if (0 : Fin (n + 1)).succ = 0 then 0 else 1) = 1
    rw [ite_eq_right (Fin.succ_ne_zero _)]
  have hx : (indexFunctor (firstCut n)).obj
      (interval 0 (firstIndex n) (Fin.zero_le _)) =
        interval (0 : Fin 2) 1 (by decide) :=
    indexObject_eq (firstCut n) (interval 0 (firstIndex n) (Fin.zero_le _))
      (interval (0 : Fin 2) 1 (by decide)) h₀ h₁
  exact (congrArg ((stageOne C).obj X).obj.obj hx).trans
    (stageOne_obj_interval_zero_one C X _)

/-- The split return's first interval keeps the original coefficient and the
actual returned diagonal `Q00`, before using any zero-unit isomorphism. -/
def splitReturnFirstIntervalIso (n : ℕ) (X : C) (Q : Stage C n) :
    ((splitReturn C n).obj (X, Q)).obj.obj
        (interval 0 (firstIndex n) (Fin.zero_le _)) ≅
      (Waldhausen.waldhausenCoproductFunctor C).obj
        (X, Q.obj.obj (diag (0 : Fin (n + 1)))) := by
  have hQ : ((degenerateReturn C n).obj Q).obj.obj
      (interval 0 (firstIndex n) (Fin.zero_le _)) = Q.obj.obj (diag (0 : Fin (n + 1))) :=
    (source_obj C n ((degenerateReturn C n).obj Q)).symm.trans
      (degenerateReturn_source_obj C n Q)
  exact splitReturnIntervalIso C n X Q (interval 0 (firstIndex n) (Fin.zero_le _)) ≪≫
    eqToIso (congrArg (Waldhausen.waldhausenCoproductFunctor C).obj
      (Prod.ext (insert_first_obj C n X) hQ))

/-- Every interval of the actual constant-zero stage retains the original diagonal `A11`. -/
theorem zeroEndo_obj (n : ℕ) (A : Stage C (n + 1)) (x : Ar (n + 1)) :
    ((zeroEndo C n).obj A).obj.obj x = A.obj.obj (diag (firstIndex n)) := by
  have hx : (indexFunctor (firstConstant n)).obj x = diag (firstIndex n) := by
    obtain ⟨i, j, f, rfl⟩ := Arrow.mk_surjective x
    rfl
  change A.obj.obj ((indexFunctor (firstConstant n)).obj x) = _
  exact congrArg A.obj.obj hx

/-- The stock cofiber lift retains the original entire first-step endofunctor. -/
theorem cofiberLift_source (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    cofiberLift C n ⋙ CofiberSequenceCategory.source (Stage C (n + 1)) = firstEndo C n := by
  let : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  exact cofiberFunctorSequenceLift_source (firstEndo C n) (𝟭 _) (quotientEndo C n)
    (sourceInclusion C n) (quotientProjection C n)
    (isWaldhausenCofiberFunctorSequence C n).objectwise

/-- The stock cofiber lift keeps the unchanged original stage as its whole middle functor. -/
theorem cofiberLift_middle (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    cofiberLift C n ⋙ CofiberSequenceCategory.middle (Stage C (n + 1)) =
      𝟭 (Stage C (n + 1)) := by
  let : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  exact cofiberFunctorSequenceLift_middle (firstEndo C n) (𝟭 _) (quotientEndo C n)
    (sourceInclusion C n) (quotientProjection C n)
    (isWaldhausenCofiberFunctorSequence C n).objectwise

/-- The stock cofiber lift retains the actual original degenerate quotient
as its whole quotient functor. -/
theorem cofiberLift_quotient (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    cofiberLift C n ⋙ CofiberSequenceCategory.quotient (Stage C (n + 1)) = quotientEndo C n := by
  let : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  exact cofiberFunctorSequenceLift_quotient (firstEndo C n) (𝟭 _) (quotientEndo C n)
    (sourceInclusion C n) (quotientProjection C n)
    (isWaldhausenCofiberFunctorSequence C n).objectwise

/-- The whole original first-entry/quotient projection is exact for the
named stage values and the actual componentwise product value. -/
theorem projection_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : WaldhausenCategoryWithoutGluing (C × Stage C n) := prodWaldhausen
    (projection C n).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let _ : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let _ : WaldhausenCategoryWithoutGluing (C × Stage C n) := prodWaldhausen
  let hF := source_isWaldhausenExact C n
  let hG := quotient_isWaldhausenExact C n
  exact hF.prod' hG

/-- The actual split return is exact under the original base gluing axiom,
using the same original componentwise and general-stage Waldhausen values. -/
theorem splitReturn_isWaldhausenExact (n : ℕ) (hGlue : WaldhausenGluingAxiom (C := C)) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : WaldhausenCategoryWithoutGluing (C × Stage C n) := prodWaldhausen
    (splitReturn C n).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
    generalStageWaldhausenCategory C (n + 1)
  let _ : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let _ : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let _ : WaldhausenCategoryWithoutGluing (C × Stage C n) := prodWaldhausen
  let _ : WaldhausenCategoryWithoutGluing (Stage C (n + 1) × Stage C (n + 1)) := prodWaldhausen
  let f₀ : C × Stage C n ⥤ Stage C (n + 1) :=
    CategoryTheory.Prod.fst C (Stage C n) ⋙ insert C n
  let f₁ : C × Stage C n ⥤ Stage C (n + 1) :=
    CategoryTheory.Prod.snd C (Stage C n) ⋙ degenerateReturn C n
  have h₀ : f₀.IsWaldhausenExact :=
    (Functor.IsWaldhausenExact.prodFst C (Stage C n)).comp (insert_isWaldhausenExact C n)
  have h₁ : f₁.IsWaldhausenExact :=
    (Functor.IsWaldhausenExact.prodSnd C (Stage C n)).comp
      (degenerateReturn_isWaldhausenExact C n)
  have hPair : (f₀.prod' f₁).IsWaldhausenExact := h₀.prod' h₁
  have hK : ((insert C n).prod (degenerateReturn C n)).IsWaldhausenExact := hPair
  exact hK.comp (Waldhausen.waldhausenCoproductFunctor_isWaldhausenExact
    (Stage C (n + 1)) (generalStageWaldhausenGluingAxiom C hGlue (n + 1)))

end StageFirstQuotient

end CategoryTheory.Waldhausen.SConstruction

end
