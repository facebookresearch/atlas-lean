/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowCoreStabilization
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowIntrinsicHomology
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Data.Nat.Init

/-!
# Actual finite-row stabilization and eventual equality of fractions

Iterating the computed numerator successor equation gives the exact regular
power action along every ORIGINAL finite-stage transition. Regular-fraction
equality and injectivity of the original core-stage homology map then give
equality at an actual common finite stage. The original homology colimit
therefore maps monomorphically to the intrinsic zero subgroup.

The argument assumes no scalar injectivity or unstabilized equality. Full
surjectivity still requires coverage of every correctly graded numerator.
-/

noncomputable section

open CategoryTheory Limits Algebra

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- Every ORIGINAL finite-stage transition acts on its core numerator by
the exact regular power corresponding to the stage difference. -/
public theorem finiteFreeRowStageCoreNumerator_stabilization
    (A : AddCommGrpCat.{u}) (q n m : ℕ) (h : n ≤ m)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    (SInverseS.coreTranslationHomologyModuleAddCommGrpIso
        (FGProjectiveCat.IdempotentModel R) A q).inv
      (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R m) A q
        (SSet.homologyMap (C := AddCommGrpCat.{u})
          ((finiteBGLNerveDiagram R).map (homOfLE h)) A q x)) =
      @SMul.smul
        ↥(SInverseS.coreTranslationDenominators (FGProjectiveCat.IdempotentModel R))
        (SInverseS.coreTranslationHomologyModuleCat
          (FGProjectiveCat.IdempotentModel R) A q)
        inferInstance ((finiteFreeRowRegularDenominator R) ^ (m - n))
        ((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u})
              (finiteFreeRowStageCoreNerveMap R n) A q x)) := by
  let C := FGProjectiveCat.IdempotentModel R
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  let D : ℕ ⥤ AddCommGrpCat.{u} := finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor
    (C := AddCommGrpCat.{u}) A q
  let N (k : ℕ) : D.obj k → SInverseS.coreTranslationHomologyModule C A q :=
    fun z => ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u})
      (finiteFreeRowStageCoreNerveMap R k) A q z)
  let r := finiteFreeRowRegularDenominator R
  let P (k : ℕ) (hk : n ≤ k) : Prop :=
    N k (D.map (homOfLE hk) x) = (r ^ (k - n)) • N n x
  change P m h
  have hBase : P n le_rfl := by
    change N n (D.map (homOfLE (show n ≤ n from le_rfl)) x) =
      (r ^ (n - n)) • N n x
    have hId : (homOfLE (show n ≤ n from le_rfl) : n ⟶ n) = 𝟙 n :=
      Subsingleton.elim _ _
    rw [hId, D.map_id]
    simp only [Nat.sub_self, pow_zero, one_smul]
    exact congrArg (N n)
      (ConcreteCategory.id_apply (C := AddCommGrpCat.{u}) (X := D.obj n) x)
  have hStep : ∀ (k : ℕ) (hk : n ≤ k),
      P k hk → P (k + 1) (Nat.le_succ_of_le hk) := by
    intro k hk ih
    change N k (D.map (homOfLE hk) x) = (r ^ (k - n)) • N n x at ih
    change N (k + 1) (D.map (homOfLE (Nat.le_succ_of_le hk)) x) =
      (r ^ (k + 1 - n)) • N n x
    let z : D.obj k := D.map (homOfLE hk) x
    have hSucc : N (k + 1) (D.map (homOfLE (Nat.le_succ k)) z) = r • N k z :=
      finiteFreeRowStageCoreNumerator_succ R A q k z
    have hComp : (homOfLE (Nat.le_succ_of_le hk) : n ⟶ k + 1) =
        homOfLE hk ≫ homOfLE (Nat.le_succ k) := Subsingleton.elim _ _
    have hMap : D.map (homOfLE (Nat.le_succ_of_le hk)) =
        D.map (homOfLE hk) ≫ D.map (homOfLE (Nat.le_succ k)) :=
      (congrArg D.map hComp).trans (D.map_comp _ _)
    have hExp : k + 1 - n = (k - n) + 1 := by omega
    rw [hMap]
    change N (k + 1) (D.map (homOfLE (Nat.le_succ k)) z) =
      (r ^ (k + 1 - n)) • N n x
    calc
      _ = r • N k z := hSucc
      _ = r • ((r ^ (k - n)) • N n x) := congrArg (fun y => r • y) ih
      _ = (r ^ ((k - n) + 1)) • N n x := by rw [← mul_smul, ← pow_succ']
      _ = (r ^ (k + 1 - n)) • N n x :=
        congrArg (fun j : ℕ => (r ^ j) • N n x) hExp.symm
  exact Nat.le_induction (m := n) (P := P) hBase hStep m h

/-- Equality of two actual intrinsic finite-stage values is EXACTLY equality
after ORIGINAL transitions to an actual common stage. Both eventual directions
are derived; no pre-stabilization injectivity is assumed. -/
public theorem finiteFreeRowIntrinsic_stage_eq_iff_common_stage
    (A : AddCommGrpCat.{u}) (q n m : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q)
    (y : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    finiteFreeRowIntrinsicHomologyComparison R A q
        (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
          A q) n x) =
      finiteFreeRowIntrinsicHomologyComparison R A q
        (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
          A q) m y) ↔
      ∃ (t : ℕ) (hn : n ≤ t) (hm : m ≤ t),
        SSet.homologyMap (C := AddCommGrpCat.{u})
          ((finiteBGLNerveDiagram R).map (homOfLE hn)) A q x =
          SSet.homologyMap (C := AddCommGrpCat.{u})
            ((finiteBGLNerveDiagram R).map (homOfLE hm)) A q y := by
  let C := FGProjectiveCat.IdempotentModel R
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  let D : ℕ ⥤ AddCommGrpCat.{u} := finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor
    (C := AddCommGrpCat.{u}) A q
  let Ψ := finiteFreeRowIntrinsicHomologyComparison R A q
  let a : CategoryTheory.SInverseS.coreTranslationHomologyModuleCat C A q :=
    ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u})
    (finiteFreeRowStageCoreNerveMap R n) A q x)
  let b : CategoryTheory.SInverseS.coreTranslationHomologyModuleCat C A q :=
    ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u})
    (finiteFreeRowStageCoreNerveMap R m) A q y)
  constructor
  · intro h
    have hFraction : LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      a ((finiteFreeRowRegularDenominator R) ^ n) =
        LocalizedModule.mk
          (R := CategoryTheory.SInverseS.coreTranslationRing
            (FGProjectiveCat.IdempotentModel R))
          (S := CategoryTheory.SInverseS.coreTranslationDenominators
            (FGProjectiveCat.IdempotentModel R))
          (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
            (FGProjectiveCat.IdempotentModel R) A q)
          b ((finiteFreeRowRegularDenominator R) ^ m) :=
      (finiteFreeRowIntrinsicHomologyComparison_ι_val R A q n x).symm.trans
        ((congrArg Subtype.val h).trans
          (finiteFreeRowIntrinsicHomologyComparison_ι_val R A q m y))
    obtain ⟨t, hn, hm, hAction⟩ :=
      (finiteFreeRowLocalization_mk_eq_iff_common_stage R a b n m).mp hFraction
    let zx := D.map (homOfLE hn) x
    let zy := D.map (homOfLE hm) y
    have hx : ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u})
      (finiteFreeRowStageCoreNerveMap R t) A q zx) =
        ((finiteFreeRowRegularDenominator R) ^ (t - n)) • a :=
      finiteFreeRowStageCoreNumerator_stabilization R A q n t hn x
    have hy : ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u})
      (finiteFreeRowStageCoreNerveMap R t) A q zy) =
        ((finiteFreeRowRegularDenominator R) ^ (t - m)) • b :=
      finiteFreeRowStageCoreNumerator_stabilization R A q m t hm y
    have hNumerator := hx.trans (hAction.trans hy.symm)
    have hCore : SSet.homologyMap (C := AddCommGrpCat.{u})
      (finiteFreeRowStageCoreNerveMap R t) A q zx =
        SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R t) A q zy :=
      (Iso.inv_hom_id_apply ε _).symm.trans
        ((congrArg ε.hom hNumerator).trans (Iso.inv_hom_id_apply ε _))
    letI : Mono (SSet.homologyMap (C := AddCommGrpCat.{u})
      (finiteFreeRowStageCoreNerveMap R t) A q) :=
      finiteFreeRowStageCoreHomology_mono R A q t
    have hInjective := (AddCommGrpCat.mono_iff_injective
      (SSet.homologyMap (C := AddCommGrpCat.{u})
        (finiteFreeRowStageCoreNerveMap R t) A q)).mp inferInstance
    exact ⟨t, hn, hm, hInjective hCore⟩
  · rintro ⟨t, hn, hm, hxy⟩
    have hx : colimit.ι D n x = colimit.ι D t (D.map (homOfLE hn) x) :=
      (ConcreteCategory.congr_hom (colimit.w D (homOfLE hn)) x).symm
    have hy : colimit.ι D m y = colimit.ι D t (D.map (homOfLE hm) y) :=
      (ConcreteCategory.congr_hom (colimit.w D (homOfLE hm)) y).symm
    exact congrArg Ψ (hx.trans ((congrArg (colimit.ι D t) hxy).trans hy.symm))

/-- In every degree the ACTUAL original finite-stage homology colimit
comparison is monic. Filtered representatives and the derived eventual
kernel equality prove this without a homology-isomorphism input. -/
public theorem finiteFreeRowIntrinsicHomologyComparison_mono
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    Mono (finiteFreeRowIntrinsicHomologyComparison R A q) := by
  let D : ℕ ⥤ AddCommGrpCat.{u} := finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor
    (C := AddCommGrpCat.{u}) A q
  let F := forget AddCommGrpCat.{u}
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits
      (forget AddCommGrpCat.{u})
  letI : PreservesColimit D F := by
    change PreservesColimit D (forget AddCommGrpCat.{u})
    infer_instance
  let hc : IsColimit (F.mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves F (colimit.isColimit D)
  let Ψ := finiteFreeRowIntrinsicHomologyComparison R A q
  apply (AddCommGrpCat.mono_iff_injective Ψ).mpr
  intro a b hab
  obtain ⟨n, x, y, hx, hy⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc a b
  change colimit.ι D n x = a at hx
  change colimit.ι D n y = b at hy
  have hStage : Ψ (colimit.ι D n x) = Ψ (colimit.ι D n y) :=
    (congrArg Ψ hx).trans (hab.trans (congrArg Ψ hy).symm)
  obtain ⟨t, hn, hm, hxy⟩ :=
    (finiteFreeRowIntrinsic_stage_eq_iff_common_stage R A q n n x y).mp hStage
  have hX : colimit.ι D t (D.map (homOfLE hn) x) = colimit.ι D n x :=
    ConcreteCategory.congr_hom (colimit.w D (homOfLE hn)) x
  have hY : colimit.ι D t (D.map (homOfLE hm) y) = colimit.ι D n y :=
    ConcreteCategory.congr_hom (colimit.w D (homOfLE hm)) y
  exact hx.symm.trans
    (hX.symm.trans ((congrArg (colimit.ι D t) hxy).trans (hY.trans hy)))

end AlgebraicKTheory.StableGL
