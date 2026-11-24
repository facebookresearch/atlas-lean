/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2026 Toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Toskua
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import MathlibExt.Algebra.Homology.Embedding.PositiveNat
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.Algebra.Homology.Embedding.PositiveStupidTruncInclusion

/-!
# The actual smart-to-stupid positive truncation comparison

The native smart truncation maps to the native restriction and hence to
its extension, the stupid truncation. Its retained components are the
original smart-truncation inclusions. For nonnegative chains with zero
boundary from degree one, the comparison is an isomorphism. Its inverse
then gives an actual inclusion of the whole positive stupid truncation.

The original degree-zero object is unrestricted. Object and morphism
universes are independent, and no tensor structure is needed.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u w w'

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C]

section Coordinates

variable [HasZeroMorphisms C]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i']

/-- At a boundary the native smart-to-restriction map is the actual cycle inclusion. -/
@[reassoc]
theorem truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv
    {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE'ToRestriction e).f i =
      (K.truncLE'XIsoCycles e hi' hi).hom ≫ K.iCycles i' ≫
        (K.restrictionXIso e hi').inv := by
  subst hi'
  have h : (K.op.restrictionToTruncGE' e.op).f i =
      (K.op.restrictionXIso e.op rfl).hom ≫ (K.iCycles (e.f i)).op ≫
        (K.opcyclesOpIso (e.f i)).inv ≫
          (K.op.truncGE'XIsoOpcycles e.op rfl (by simpa using hi)).inv := by
    have hn := K.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
      e.op (i := i) (i' := e.f i) rfl (by simpa using hi)
    have hb := congrArg
      (fun f => (K.op.restrictionXIso e.op rfl).hom ≫ f ≫
        (K.opcyclesOpIso (e.f i)).inv ≫
          (K.op.truncGE'XIsoOpcycles e.op rfl (by simpa using hi)).inv)
      (CategoryTheory.ShortComplex.op_pOpcycles_opcyclesOpIso_hom (K.sc (e.f i)))
    change (K.op.restrictionXIso e.op (i := i) (i' := e.f i) rfl).hom ≫
        (K.op.pOpcycles (e.f i) ≫ (K.opcyclesOpIso (e.f i)).hom) ≫
          (K.opcyclesOpIso (e.f i)).inv ≫
            (K.op.truncGE'XIsoOpcycles e.op (i := i) (i' := e.f i)
              rfl (by simpa using hi)).inv =
      (K.op.restrictionXIso e.op (i := i) (i' := e.f i) rfl).hom ≫
        (K.iCycles (e.f i)).op ≫ (K.opcyclesOpIso (e.f i)).inv ≫
          (K.op.truncGE'XIsoOpcycles e.op (i := i) (i' := e.f i)
            rfl (by simpa using hi)).inv at hb
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at hb
    exact hn.trans hb
  apply Quiver.Hom.op_inj
  simpa [truncLE'ToRestriction, unopFunctor, truncLE'XIsoCycles,
    truncLE', restriction, restrictionXIso, Category.assoc] using! h

/-- Away from a boundary the actual map is the original coordinate isomorphism. -/
@[reassoc]
theorem truncLE'ToRestriction_f_eq_iso_hom_iso_inv
    {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE'ToRestriction e).f i =
      (K.truncLE'XIso e hi' hi).hom ≫ (K.restrictionXIso e hi').inv := by
  subst hi'
  apply Quiver.Hom.op_inj
  simpa [truncLE'ToRestriction, unopFunctor, truncLE'XIso, truncLE',
    restriction, restrictionXIso] using!
    K.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op rfl (by simpa using hi)

variable [HasZeroObject C]

private theorem extend_XIso_hom_op_comp_XOpIso_inv
    {κ : Type*} {d : ComplexShape κ} (A : HomologicalComplex C d)
    {x : Option κ} {i : κ} (hx : x = some i) :
    (extend.XIso A hx).hom.op ≫ (extend.XOpIso A x).inv =
      (extend.XIso A.op hx).inv := by
  subst x
  change (𝟙 (Opposite.op (A.X i))) ≫ 𝟙 (Opposite.op (A.X i)) =
    𝟙 (Opposite.op (A.X i))
  exact Category.id_comp _

private theorem extendXIso_hom_op_comp_extendOpIso_inv
    {κ : Type*} {κ' : Type*} {d : ComplexShape κ} {d' : ComplexShape κ'}
    (A : HomologicalComplex C d) (a : d.Embedding d') (i : κ) :
    (A.extendXIso a rfl).hom.op ≫ (A.extendOpIso a).inv.f (a.f i) =
      (A.op.extendXIso a.op rfl).inv := by
  simpa only [extendXIso, extendOpIso, Hom.isoOfComponents,
    ComplexShape.Embedding.op] using!
    extend_XIso_hom_op_comp_XOpIso_inv A (a.r_eq_some rfl)

private theorem truncLEIso_hom_f_comp_extendXIso_hom (i : ι) :
    (K.truncLEIso e).hom.f (e.f i) ≫ ((K.truncLE' e).extendXIso e rfl).hom =
      ((K.op.truncGE' e.op).extendXIso e.op rfl).inv.unop := by
  apply Quiver.Hom.op_inj
  change ((K.truncLE' e).extendXIso e rfl).hom.op ≫
      ((K.truncLE' e).extendOpIso e).inv.f (e.f i) =
    ((K.op.truncGE' e.op).extendXIso e.op rfl).inv
  exact extendXIso_hom_op_comp_extendOpIso_inv (K.truncLE' e) e i

/-- The original smart-to-restriction map, extended along the same native embedding. -/
def truncLEToStupid : K.truncLE e ⟶ K.stupidTrunc e :=
  (K.truncLEIso e).hom ≫ extendMap (K.truncLE'ToRestriction e) e

/-- The retained component of the actual comparison is the original smart inclusion. -/
@[reassoc]
theorem truncLEToStupid_f_comp_stupidTruncXIso_hom
    {i : ι} {i' : ι'} (hi' : e.f i = i') :
    (K.truncLEToStupid e).f i' ≫ (K.stupidTruncXIso e hi').hom =
      (K.ιTruncLE e).f i' := by
  subst hi'
  have h : ((K.truncLEIso e).hom ≫
      extendMap (K.truncLE'ToRestriction e) e).f (e.f i) ≫
        (((K.restriction e).extendXIso e rfl).hom ≫
          (K.restrictionXIso e rfl).hom) =
            (K.ιTruncLE e).f (e.f i) := by
    rw [comp_f, extendMap_f _ e rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, truncLEIso_hom_f_comp_extendXIso_hom]
    have hU : (K.truncLE'ToRestriction e).f i =
        ((K.op.restrictionToTruncGE' e.op).f i).unop := rfl
    have hι : (K.ιTruncLE e).f (e.f i) =
        ((K.op.πTruncGE e.op).f (e.f i)).unop := rfl
    have hR : (K.restrictionXIso e rfl).hom =
        ((K.op.restrictionXIso e.op (i := i) (i' := e.f i) rfl).inv).unop := rfl
    rw [hU, hι, hR]
    change @Eq
      (Opposite.unop (((K.op.truncGE' e.op).extend e.op).X (e.f i)) ⟶
        Opposite.unop (K.op.X (e.f i)))
      (((K.op.truncGE' e.op).extendXIso e.op rfl).inv.unop ≫
        ((K.op.restrictionToTruncGE' e.op).f i).unop ≫
          ((K.op.restrictionXIso e.op (i := i) (i' := e.f i) rfl).inv).unop)
      ((K.op.πTruncGE e.op).f (e.f i)).unop
    convert congrArg Quiver.Hom.unop
      (e.op.liftExtend_f (K.op.restrictionToTruncGE' e.op)
        (K.op.restrictionToTruncGE'_hasLift e.op)
          (i := i) (i' := e.f i) rfl).symm using 1
    simp only [unop_comp, Category.assoc, πTruncGE]
    rfl
  simpa only [truncLEToStupid, stupidTruncXIso, Iso.trans_hom,
    restrictionXIso] using! h

variable {K} {L : HomologicalComplex C c'} [∀ i', L.HasHomology i']

/-- The actual comparison commutes with every original chain map. -/
@[reassoc]
theorem truncLEToStupid_naturality (φ : K ⟶ L) :
    truncLEMap φ e ≫ L.truncLEToStupid e =
      K.truncLEToStupid e ≫ stupidTruncMap φ e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    apply (cancel_mono (L.stupidTruncXIso e hi).hom).1
    change ((truncLEMap φ e).f i' ≫ (L.truncLEToStupid e).f i') ≫
        (L.stupidTruncXIso e hi).hom =
      ((K.truncLEToStupid e).f i' ≫ (stupidTruncMap φ e).f i') ≫
        (L.stupidTruncXIso e hi).hom
    calc
      _ = (truncLEMap φ e).f i' ≫ (L.ιTruncLE e).f i' := by
        rw [Category.assoc, truncLEToStupid_f_comp_stupidTruncXIso_hom]
      _ = (K.ιTruncLE e).f i' ≫ φ.f i' :=
        congrArg (fun f : K.truncLE e ⟶ L => f.f i') (ιTruncLE_naturality φ e)
      _ = ((K.truncLEToStupid e).f i' ≫ (K.stupidTruncXIso e hi).hom) ≫ φ.f i' := by
        rw [truncLEToStupid_f_comp_stupidTruncXIso_hom]
      _ = _ := by
        simp only [Category.assoc, stupidTruncMap_stupidTruncXIso_hom]
  · exact (L.isZero_stupidTrunc_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_tgt _ _

end Coordinates

section Positive

variable [Abelian C]

local notation "e₊" => ComplexShape.positiveNatEmbedding

private theorem positive_boundary_zero : e₊.BoundaryLE 0 :=
  e₊.boundaryLE (k' := 0) (by change 0 + 1 = 0 + 1; rfl)
    (by intro i; change i + 1 ≠ 0; omega)

private theorem positive_not_boundary_succ (i : ℕ) : ¬ e₊.BoundaryLE (i + 1) :=
  e₊.not_boundaryLE_prev (j := i) (by change i + 1 = i + 1; rfl)

variable (K : ChainComplex C ℕ)

/-- Zero original boundary from degree one makes the actual smart-to-restriction map invertible. -/
theorem isIso_truncLE'ToRestriction_positive (hK : K.d 1 0 = 0) :
    IsIso (K.truncLE'ToRestriction e₊) := by
  suffices ∀ i : ℕ, IsIso ((K.truncLE'ToRestriction e₊).f i) by
    apply Hom.isIso_of_components
  intro i
  cases i with
  | zero =>
      rw [truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv K e₊ rfl
        positive_boundary_zero]
      let hCycles : IsIso (K.iCycles (e₊.f 0)) := by
        change IsIso (K.iCycles 1)
        exact K.isIso_iCycles 1 0
          ((ComplexShape.down ℕ).next_eq' (by change 0 + 1 = 1; rfl)) hK
      infer_instance
  | succ i =>
      exact K.isIso_truncLE'ToRestriction e₊ (i + 1) (positive_not_boundary_succ i)

/-- The actual extended comparison is invertible under the original endpoint-zero law. -/
theorem isIso_truncLEToStupid_positive (hK : K.d 1 0 = 0) :
    IsIso (K.truncLEToStupid e₊) := by
  let hRestriction : IsIso (K.truncLE'ToRestriction e₊) :=
    K.isIso_truncLE'ToRestriction_positive hK
  let hExtend : IsIso (extendMap (K.truncLE'ToRestriction e₊) e₊) :=
    inferInstanceAs (IsIso ((e₊.extendFunctor C).map (K.truncLE'ToRestriction e₊)))
  dsimp only [truncLEToStupid]
  exact IsIso.comp_isIso' (K.truncLEIso e₊).isIso_hom hExtend

/-- The canonical isomorphism obtained from the actual comparison and the endpoint-zero law. -/
def positiveTruncLEToStupidIso (hK : K.d 1 0 = 0) : K.truncLE e₊ ≅ K.stupidTrunc e₊ :=
  letI := K.isIso_truncLEToStupid_positive hK
  asIso (K.truncLEToStupid e₊)

/-- Its forward map is the original comparison, without any caller-supplied isomorphism. -/
@[simp]
theorem positiveTruncLEToStupidIso_hom (hK : K.d 1 0 = 0) :
    (K.positiveTruncLEToStupidIso hK).hom = K.truncLEToStupid e₊ := rfl

/-- Under abelian homology assumptions, the direct inclusion agrees with the earned smart inverse. -/
theorem positiveStupidTruncInclusion_eq_inverse_comp (hK : K.d 1 0 = 0) :
    K.positiveStupidTruncInclusion hK =
      (K.positiveTruncLEToStupidIso hK).inv ≫ K.ιTruncLE e₊ := by
  ext i'
  by_cases hi' : ∃ i, e₊.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    change stupidTruncι.f K e₊ i' =
      ((K.positiveTruncLEToStupidIso hK).inv ≫ K.ιTruncLE e₊).f i'
    rw [stupidTruncι.f_eq K e₊ hi]
    let hComparison := K.isIso_truncLEToStupid_positive hK
    let hComponent : IsIso ((K.truncLEToStupid e₊).f i') :=
      inferInstanceAs (IsIso ((eval C (ComplexShape.down ℕ) i').map
        (K.truncLEToStupid e₊)))
    apply (cancel_epi ((K.truncLEToStupid e₊).f i')).1
    have hb : (K.truncLEToStupid e₊).f i' ≫
        (((K.positiveTruncLEToStupidIso hK).inv ≫ K.ιTruncLE e₊).f i') =
          (K.ιTruncLE e₊).f i' := by
      have h := congrArg (fun f : K.truncLE e₊ ⟶ K => f.f i')
        ((K.positiveTruncLEToStupidIso hK).hom_inv_id_assoc (K.ιTruncLE e₊))
      simpa only [comp_f, Category.assoc, positiveTruncLEToStupidIso_hom] using h
    rw [hb]
    exact K.truncLEToStupid_f_comp_stupidTruncXIso_hom e₊ hi
  · exact (K.isZero_stupidTrunc_X e₊ i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src _ _

/-- The comparison followed by the direct strict inclusion is the original smart inclusion. -/
@[reassoc]
theorem truncLEToStupid_comp_positiveStupidTruncInclusion (hK : K.d 1 0 = 0) :
    K.truncLEToStupid e₊ ≫ K.positiveStupidTruncInclusion hK = K.ιTruncLE e₊ := by
  rw [positiveStupidTruncInclusion_eq_inverse_comp K hK]
  change (K.positiveTruncLEToStupidIso hK).hom ≫
    ((K.positiveTruncLEToStupidIso hK).inv ≫ K.ιTruncLE e₊) = K.ιTruncLE e₊
  exact Iso.hom_inv_id_assoc _ _

end Positive

end HomologicalComplex
