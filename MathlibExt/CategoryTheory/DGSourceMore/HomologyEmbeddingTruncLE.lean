/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/Embedding/TruncLE.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Good truncation of complexes

Let `e : c.Embedding c'` be an embedding of complex shapes with `e.IsTruncLE`, and let `K` be a
homological complex of shape `c'`.  Mathlib's canonical truncation `K.truncLE' e` agrees with the
restriction `K.restriction e` away from the boundary of `e`, and has the cycles of `K` at the
boundary; the comparison `K.truncLE'ToRestriction e` is a monomorphism in each degree.

This file describes that comparison in each degree and proves the universal property it implies:
a morphism `φ : A ⟶ K.restriction e` factors through `K.truncLE' e` as soon as each boundary
component of `φ` is killed by the differential of `K`.

For the embedding `ComplexShape.embeddingDownNat : n ↦ -n` of chain complexes indexed by `ℕ` into
cochain complexes indexed by `ℤ`, the truncation `K.truncLE' embeddingDownNat` is the good
truncation `τ_{≥ 0} K` in homological grading: its degree `n > 0` is `K^{-n}`, its degree `0` is
the cycles `Z⁰ K`, and its homology in degree `n` is `H^{-n} K`.  The last section records the
inclusion of each of its degrees into `K` and how it meets the differentials.
`HomologicalComplex.truncLE'HomologyIso` gives the homology comparison for an arbitrary
embedding of complex shapes, including boundary degrees, naturally in `K`.

## Main definitions and results

* `HomologicalComplex.truncLE'ToRestriction_f_eq_iso_hom_iso_inv` and
  `HomologicalComplex.truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv`: the components of
  `K.truncLE'ToRestriction e` away from and at the boundary.
* `HomologicalComplex.truncLE'ToRestriction_f_comp_d`: at the boundary, the comparison is killed
  by the differential of `K`.
* `HomologicalComplex.liftTruncLE'`: the factorization of a morphism into `K.restriction e`
  whose boundary components are killed by the differential, and
  `HomologicalComplex.liftTruncLE'_truncLE'ToRestriction`, its defining property.
* `ComplexShape.boundaryLE_embeddingDownNat_iff`: the boundary of `embeddingDownNat` is `0`.
* `CochainComplex.truncLE'ToX`: the inclusion of degree `n` of `τ_{≥ 0} K` into `K^{-n}`, with
  `CochainComplex.truncLE'ToX_d_succ` and `CochainComplex.truncLE'ToX_zero_d` for the
  differentials.
-/
public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE] [∀ i', K.HasHomology i']

/-- Away from the boundary, the comparison `K.truncLE' e ⟶ K.restriction e` is the identity of
`K.X i'` up to the canonical isomorphisms. -/
lemma truncLE'ToRestriction_f_eq_iso_hom_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i')
    (hi : ¬ e.BoundaryLE i) :
    (K.truncLE'ToRestriction e).f i =
      (K.truncLE'XIso e hi' hi).hom ≫ (K.restrictionXIso e hi').inv := by
  -- Mathlib defines `truncLE'` and its comparison maps by dualizing `truncGE'`, so we dualize the
  -- description of `restrictionToTruncGE'` away from the boundary.
  have h := congrArg Quiver.Hom.unop
    (K.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hi' (by simpa using hi))
  subst hi'
  refine h.trans ?_
  simp only [restrictionXIso, eqToIso.hom, eqToIso.inv, unop_comp, eqToHom_unop]
  -- `(K.truncLE'XIso e _ hi).hom` is by definition `(K.op.truncGE'XIso e.op _ _).inv.unop`.
  rfl

/-- At the boundary, the comparison `K.truncLE' e ⟶ K.restriction e` is the inclusion of the
cycles of `K`, up to the canonical isomorphisms. -/
lemma truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i')
    (hi : e.BoundaryLE i) :
    (K.truncLE'ToRestriction e).f i =
      (K.truncLE'XIsoCycles e hi' hi).hom ≫ K.iCycles i' ≫ (K.restrictionXIso e hi').inv := by
  have hi₀ : e.op.BoundaryGE i := by simpa using hi
  -- Mathlib defines `truncLE'` and its comparison maps by dualizing `truncGE'`, so we dualize the
  -- description of `restrictionToTruncGE'` at the boundary; pass through `opcyclesOpIso` first.
  have h₁ : (K.opcyclesOpIso i').inv.unop ≫ K.iCycles i' = (K.op.pOpcycles i').unop := by
    have h : K.op.pOpcycles i' ≫ (K.opcyclesOpIso i').hom = (K.iCycles i').op :=
      (K.sc i').op_pOpcycles_opcyclesOpIso_hom
    rw [← Quiver.Hom.unop_op (K.iCycles i'), ← h, ← unop_comp]
    simp
  have h₂ : (K.truncLE'XIsoCycles e hi' hi).hom ≫ K.iCycles i' =
      (K.op.truncGE'XIsoOpcycles e.op hi' hi₀).inv.unop ≫ (K.op.pOpcycles i').unop :=
    (Category.assoc _ _ _).trans (congrArg _ h₁)
  have h₃ := congrArg Quiver.Hom.unop
    (K.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e.op hi' hi₀)
  rw [← Category.assoc, h₂]
  subst hi'
  refine h₃.trans ?_
  simp only [restrictionXIso, eqToIso.hom, eqToIso.inv, unop_comp, Category.assoc]
  exact (Category.assoc _ _ _).symm

/-- At the boundary, the comparison `K.truncLE' e ⟶ K.restriction e` lands in the cycles of `K`:
it is killed by the differential of `K`. -/
@[reassoc (attr := simp)]
lemma truncLE'ToRestriction_f_comp_d {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i)
    (j' : ι') :
    (K.truncLE'ToRestriction e).f i ≫ (K.restrictionXIso e hi').hom ≫ K.d i' j' = 0 := by
  simp [K.truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv e hi' hi]

instance : Mono (K.truncLE'ToRestriction e) := mono_of_mono_f _ inferInstance

variable {K e} {A : HomologicalComplex C c} (φ : A ⟶ K.restriction e)
  (hφ : ∀ i, e.BoundaryLE i → ∀ i' (hi' : e.f i = i') j',
    φ.f i ≫ (K.restrictionXIso e hi').hom ≫ K.d i' j' = 0)

namespace liftTruncLE'

open scoped Classical in
/-- Auxiliary definition for `HomologicalComplex.liftTruncLE'`. -/
private noncomputable def f (i : ι) : A.X i ⟶ (K.truncLE' e).X i :=
  if hi : e.BoundaryLE i then
    K.liftCycles (φ.f i ≫ (K.restrictionXIso e rfl).hom) _ rfl (by simpa using hφ i hi _ rfl _) ≫
      (K.truncLE'XIsoCycles e rfl hi).inv
  else
    φ.f i ≫ (K.restrictionXIso e rfl).hom ≫ (K.truncLE'XIso e rfl hi).inv

open scoped Classical in
/-- `HomologicalComplex.liftTruncLE'.f` lifts the components of `φ`. -/
@[reassoc]
private lemma f_comp (i : ι) : f φ hφ i ≫ (K.truncLE'ToRestriction e).f i = φ.f i := by
  by_cases hi : e.BoundaryLE i
  · rw [f, dite_eq_left hi, K.truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv e rfl hi]
    simp
  · rw [f, dite_eq_right hi, K.truncLE'ToRestriction_f_eq_iso_hom_iso_inv e rfl hi]
    simp

end liftTruncLE'

/-- A morphism `φ : A ⟶ K.restriction e` whose components at the boundary of `e` are killed by
the differential of `K` factors through the canonical truncation `K.truncLE' e`. -/
noncomputable def liftTruncLE' : A ⟶ K.truncLE' e where
  f := liftTruncLE'.f φ hφ
  comm' i j _ := by
    rw [← cancel_mono ((K.truncLE'ToRestriction e).f j), Category.assoc, Category.assoc,
      ← (K.truncLE'ToRestriction e).comm, liftTruncLE'.f_comp_assoc, liftTruncLE'.f_comp, φ.comm]

/-- The defining property of `HomologicalComplex.liftTruncLE'`; it determines the lift, since
`K.truncLE'ToRestriction e` is a monomorphism. -/
@[reassoc (attr := simp)]
lemma liftTruncLE'_truncLE'ToRestriction :
    liftTruncLE' φ hφ ≫ K.truncLE'ToRestriction e = φ := by
  ext i
  exact liftTruncLE'.f_comp φ hφ i

section Homology

variable [HasZeroObject C]

/-- The comparison of good truncation with extension by zero is natural. -/
@[reassoc]
lemma truncLEIso_hom_naturality {L : HomologicalComplex C c'} [∀ i, L.HasHomology i]
    (φ : K ⟶ L) :
    truncLEMap φ e ≫ (L.truncLEIso e).hom =
      (K.truncLEIso e).hom ≫ extendMap (truncLE'Map φ e) e := by
  ext i
  -- Both the truncation and its comparison with extension are defined by dualizing extension.
  -- Express their components using the same optional degree so that it can be eliminated.
  change (extend.mapX (truncGE'Map ((opFunctor C c').map φ.op) e.op) (e.r i)).unop ≫
      (extend.XOpIso (L.truncLE' e) (e.r i)).inv.unop =
    (extend.XOpIso (K.truncLE' e) (e.r i)).inv.unop ≫
      extend.mapX (truncLE'Map φ e) (e.r i)
  cases e.r i <;> dsimp [extend.XOpIso, extend.mapX, extend.X, truncLE'Map, unopFunctor]
  · exact (Limits.isZero_zero Cᵒᵖ).unop.eq_of_src _ _
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

variable (K e)

/-- Good truncation preserves homology at every degree of the embedded complex shape,
including its boundary degrees. -/
noncomputable def truncLE'HomologyIso (i : ι) :
    (K.truncLE' e).homology i ≅ K.homology (e.f i) :=
  ((K.truncLE' e).extendHomologyIso e (j := i) rfl).symm ≪≫
    homologyMapIso (K.truncLEIso e).symm (e.f i) ≪≫
      asIso (homologyMap (K.ιTruncLE e) (e.f i))

variable {K e}

/-- The homology comparison for good truncation is natural in the original complex. -/
@[reassoc]
lemma truncLE'HomologyIso_hom_naturality {L : HomologicalComplex C c'}
    [∀ i, L.HasHomology i] (φ : K ⟶ L) (i : ι) :
    homologyMap (truncLE'Map φ e) i ≫ (L.truncLE'HomologyIso e i).hom =
      (K.truncLE'HomologyIso e i).hom ≫ homologyMap φ (e.f i) := by
  have ht : extendMap (truncLE'Map φ e) e ≫ (L.truncLEIso e).inv =
      (K.truncLEIso e).inv ≫ truncLEMap φ e := by
    apply (cancel_epi (K.truncLEIso e).hom).1
    rw [← Category.assoc, ← truncLEIso_hom_naturality]
    simp
  have hc : extendMap (truncLE'Map φ e) e ≫ (L.truncLEIso e).inv ≫ L.ιTruncLE e =
      (K.truncLEIso e).inv ≫ K.ιTruncLE e ≫ φ := by
    rw [← Category.assoc, ht, Category.assoc, ιTruncLE_naturality]
  rw [← cancel_epi ((K.truncLE' e).extendHomologyIso e (j := i) rfl).hom,
    ← Category.assoc, ← extendHomologyIso_hom_naturality]
  simp only [truncLE'HomologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom, asIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [homologyMap_comp, Category.assoc] using
    congrArg (fun g ↦ homologyMap g (e.f i)) hc

end Homology

end HomologicalComplex

namespace ComplexShape

/-- The only boundary degree of the embedding `n ↦ -n` of `ComplexShape.down ℕ` into
`ComplexShape.up ℤ` is `0`. -/
lemma boundaryLE_embeddingDownNat_iff (n : ℕ) :
    embeddingDownNat.BoundaryLE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      simp at this
  · rintro rfl
    constructor
    · simp
    · intro i hi
      simp at hi
      omega

end ComplexShape

namespace CochainComplex

open ComplexShape HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : CochainComplex C ℤ) [∀ i, K.HasHomology i]

/-- The inclusion of degree `n` of the good truncation `τ_{≥ 0} K = K.truncLE' embeddingDownNat`
into `K^{-n}`: an isomorphism for `n > 0`, and the inclusion of the cycles for `n = 0`. -/
noncomputable def truncLE'ToX (n : ℕ) : (K.truncLE' embeddingDownNat).X n ⟶ K.X (-n) :=
  (K.truncLE'ToRestriction embeddingDownNat).f n ≫
    (K.restrictionXIso embeddingDownNat (embeddingDownNat_f n)).hom

/-- `CochainComplex.truncLE'ToX` is the comparison with the restriction, followed by the
identification of degree `n` of the restriction with `K^{-n}`. -/
lemma truncLE'ToX_def (n : ℕ) :
    K.truncLE'ToX n = (K.truncLE'ToRestriction embeddingDownNat).f n ≫
      (K.restrictionXIso embeddingDownNat (embeddingDownNat_f n)).hom := (rfl)

instance (n : ℕ) : Mono (K.truncLE'ToX n) := by
  rw [truncLE'ToX_def]
  infer_instance

/-- The inclusions `CochainComplex.truncLE'ToX` commute with the differentials in positive
degrees. -/
@[reassoc]
lemma truncLE'ToX_d_succ (n : ℕ) :
    K.truncLE'ToX (n + 1) ≫ K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (K.truncLE' embeddingDownNat).d (n + 1) n ≫ K.truncLE'ToX n := by
  have := (K.truncLE'ToRestriction embeddingDownNat).comm (n + 1) n
  rw [K.restriction_d_eq embeddingDownNat (embeddingDownNat_f (n + 1)) (embeddingDownNat_f n)]
    at this
  simp only [truncLE'ToX, Category.assoc]
  rw [← reassoc_of% this]
  simp

/-- Degree `0` of the good truncation lands in the cycles: it is killed by the differential. -/
@[reassoc]
lemma truncLE'ToX_zero_d (j : ℤ) : K.truncLE'ToX 0 ≫ K.d (-((0 : ℕ) : ℤ)) j = 0 := by
  rw [truncLE'ToX, Category.assoc]
  exact K.truncLE'ToRestriction_f_comp_d _ _ ((boundaryLE_embeddingDownNat_iff 0).2 rfl) j

variable {K} in
/-- The inclusions `CochainComplex.truncLE'ToX` are natural. -/
@[reassoc (attr := simp)]
lemma truncLE'Map_f_truncLE'ToX {L : CochainComplex C ℤ} [∀ i, L.HasHomology i] (f : K ⟶ L)
    (n : ℕ) :
    (truncLE'Map f embeddingDownNat).f n ≫ L.truncLE'ToX n = K.truncLE'ToX n ≫ f.f (-n) := by
  have := congr_arg (fun g => g.f n) (truncLE'ToRestriction_naturality f embeddingDownNat)
  simp only [comp_f, restrictionMap_f' f embeddingDownNat (embeddingDownNat_f n)] at this
  simp [truncLE'ToX, reassoc_of% this]

end CochainComplex
