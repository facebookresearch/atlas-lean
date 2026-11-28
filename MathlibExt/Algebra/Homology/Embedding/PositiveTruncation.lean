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
public import MathlibExt.CategoryTheory.DGSourceMore.HomologyEmbeddingTruncLE
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.Algebra.Homology.Embedding.PositiveStupidTruncInclusion

/-!
# Good and stupid positive truncations

For an incoming-closed shape embedding e, good truncation includes cycles
at an outgoing boundary while stupid truncation keeps the entire term.
Their canonical comparison agrees with the original inclusions in each
retained degree.

For nonnegative chains and e(n)=n+1, vanishing of d_1 makes the boundary
cycles equal to K_1. The good positive truncation is then canonically
isomorphic to the stupid positive truncation.
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

attribute [reassoc] truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv
attribute [reassoc] truncLE'ToRestriction_f_eq_iso_hom_iso_inv

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

/--
Let C have zero morphisms, let K be a c'-complex with homology in every degree, and let e:c→c'
preserve and reflect relations with image closed under incoming differentials (IsTruncLE). Let
κ:K.truncLE' e→K.restriction e be the comparison from the good restricted truncation. Assume
also that C has a zero object, so these complexes can be extended by zero to shape c'.
Extending κ along e, preceded by the canonical realization of the good truncation, gives
K.truncLE e→K.stupidTrunc e. It compares the boundary cycles with the entire boundary term and
is the identity comparison at other retained degrees.
-/
def truncLEToStupid : K.truncLE e ⟶ K.stupidTrunc e :=
  (K.truncLEIso e).hom ≫ extendMap (K.truncLE'ToRestriction e) e

/--
Let C have zero morphisms, let K be a c'-complex with homology in every degree, and let e:c→c'
preserve and reflect relations with image closed under incoming differentials (IsTruncLE). Let
κ:K.truncLE' e→K.restriction e be the comparison from the good restricted truncation. Assume
also that C has a zero object, so these complexes can be extended by zero to shape c'. At a
retained degree i'=e(i), the comparison component followed by the stupid coordinate
isomorphism equals the canonical good-truncation inclusion into K: (truncLEToStupid e).f i' ≫
θ_S.hom = (K.ιTruncLE e).f i'.
-/
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

/--
Let C have zero morphisms and a zero object, let e:c→c' be incoming-closed and
relation-reflecting, and let φ:K→L be a morphism of c'-complexes with homology in every
degree. The comparisons commute with φ: truncLEMap(φ,e) ≫ κ_L = κ_K ≫ stupidTruncMap(φ,e).
-/
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

/--
Let K be a nonnegative chain complex in an abelian category C, assume K.d 1 0 = 0, and let
e(n)=n+1 select the positive degrees. The comparison K.truncLE' e→K.restriction e is an
isomorphism. At its first degree the good term is Z₁(K)=K₁ because d₁=0, and all higher terms
are unchanged.
-/
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

/--
Let K be a nonnegative chain complex in an abelian category C, assume K.d 1 0 = 0, and let
e(n)=n+1 select the positive degrees. The canonical comparison K.truncLE e→K.stupidTrunc e is
an isomorphism, including the zero term at original degree zero.
-/
theorem isIso_truncLEToStupid_positive (hK : K.d 1 0 = 0) :
    IsIso (K.truncLEToStupid e₊) := by
  let hRestriction : IsIso (K.truncLE'ToRestriction e₊) :=
    K.isIso_truncLE'ToRestriction_positive hK
  let hExtend : IsIso (extendMap (K.truncLE'ToRestriction e₊) e₊) :=
    inferInstanceAs (IsIso ((e₊.extendFunctor C).map (K.truncLE'ToRestriction e₊)))
  dsimp only [truncLEToStupid]
  exact IsIso.comp_isIso' (K.truncLEIso e₊).isIso_hom hExtend

/--
Let K be a nonnegative chain complex in an abelian category C, assume K.d 1 0 = 0, and let
e(n)=n+1 select the positive degrees. The canonical good-to-stupid comparison defines an
isomorphism K.truncLE e ≅ K.stupidTrunc e, with the original comparison as its forward map.
-/
def positiveTruncLEToStupidIso (hK : K.d 1 0 = 0) : K.truncLE e₊ ≅ K.stupidTrunc e₊ :=
  letI := K.isIso_truncLEToStupid_positive hK
  asIso (K.truncLEToStupid e₊)

/--
Let K be a nonnegative chain complex in an abelian category C, assume K.d 1 0 = 0, and let
e(n)=n+1 select the positive degrees. The forward morphism of the canonical isomorphism
K.truncLE e≅K.stupidTrunc e is exactly K.truncLEToStupid e.
-/
@[simp]
theorem positiveTruncLEToStupidIso_hom (hK : K.d 1 0 = 0) :
    (K.positiveTruncLEToStupidIso hK).hom = K.truncLEToStupid e₊ := rfl

/--
Let K be a nonnegative chain complex in an abelian category C, assume K.d 1 0 = 0, and let
e(n)=n+1 select the positive degrees. The direct positive-coordinate inclusion into K equals
the inverse good-to-stupid comparison followed by the good inclusion: ι₊ =
(positiveTruncLEToStupidIso).inv ≫ K.ιTruncLE e.
-/
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

/--
Let K be a nonnegative chain complex in an abelian category C, assume K.d 1 0 = 0, and let
e(n)=n+1 select the positive degrees. The good-to-stupid comparison followed by the direct
positive inclusion equals the good inclusion into K: K.truncLEToStupid e ≫ ι₊ = K.ιTruncLE e.
-/
@[reassoc]
theorem truncLEToStupid_comp_positiveStupidTruncInclusion (hK : K.d 1 0 = 0) :
    K.truncLEToStupid e₊ ≫ K.positiveStupidTruncInclusion hK = K.ιTruncLE e₊ := by
  rw [positiveStupidTruncInclusion_eq_inverse_comp K hK]
  change (K.positiveTruncLEToStupidIso hK).hom ≫
    ((K.positiveTruncLEToStupidIso hK).inv ≫ K.ιTruncLE e₊) = K.ιTruncLE e₊
  exact Iso.hom_inv_id_assoc _ _

end Positive

end HomologicalComplex
