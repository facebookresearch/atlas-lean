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
Modifications: module paths are adapted for Atlas. The two truncation-component
formulas are imported from the general homological-complex module; the remaining
mathematical statements and maps are retained.
-/

public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import MathlibExt.Algebra.Homology.Embedding.PositiveTruncation

/-!
# Good truncation along an embedding of complex shapes

For a complex-shape embedding `e` of truncation type `IsTruncLE`,
the canonical truncation of `K` agrees with its restriction away
from the boundary and has cycles at the boundary. Its comparison
into the restriction is degreewise mono. A map into the restriction
factors through this comparison exactly when its boundary components
are killed by the outgoing differentials.

With a zero object and the displayed homologies, truncation preserves
homology at all embedded degrees and is natural in `K`. For the
embedding `n ↦ -n` from `down ℕ` to `up ℤ`, the chain truncation has
`K^(-n)` for `n>0`, `Z⁰K` in degree zero, and inclusions compatible
with the original integer cochain differentials.
-/
public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE] [∀ i', K.HasHomology i']

/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. At a boundary degree `i`, identifying its image with `i′`,
the component of the truncation comparison into `K(i′)` is killed
by every outgoing differential `K(i′) → K(j′)`. -/
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
/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. For a map `φ : A → K|_e` whose boundary components are
annihilated by the outgoing differentials of `K`, each component
lifts to the truncation term, through its cycle object at a boundary. -/
private noncomputable def f (i : ι) : A.X i ⟶ (K.truncLE' e).X i :=
  if hi : e.BoundaryLE i then
    K.liftCycles (φ.f i ≫ (K.restrictionXIso e rfl).hom) _ rfl (by simpa using hφ i hi _ rfl _) ≫
      (K.truncLE'XIsoCycles e rfl hi).inv
  else
    φ.f i ≫ (K.restrictionXIso e rfl).hom ≫ (K.truncLE'XIso e rfl hi).inv

open scoped Classical in
/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. The componentwise lift of such a boundary-annihilated
`φ : A → K|_e` followed by the truncation comparison is the
original component of `φ`. -/
@[reassoc]
private lemma f_comp (i : ι) : f φ hφ i ≫ (K.truncLE'ToRestriction e).f i = φ.f i := by
  by_cases hi : e.BoundaryLE i
  · rw [f, dite_eq_left hi, K.truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv e rfl hi]
    simp
  · rw [f, dite_eq_right hi, K.truncLE'ToRestriction_f_eq_iso_hom_iso_inv e rfl hi]
    simp

end liftTruncLE'

/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. A map `φ : A → K|_e` whose boundary components are killed
by every outgoing differential factors as a complex map
`A → τ_eK → K|_e`. -/
noncomputable def liftTruncLE' : A ⟶ K.truncLE' e where
  f := liftTruncLE'.f φ hφ
  comm' i j _ := by
    rw [← cancel_mono ((K.truncLE'ToRestriction e).f j), Category.assoc, Category.assoc,
      ← (K.truncLE'ToRestriction e).comm, liftTruncLE'.f_comp_assoc, liftTruncLE'.f_comp, φ.comm]

/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. For a boundary-annihilated map `φ : A → K|_e`, its lift
satisfies `lift(φ) ≫ (τ_eK → K|_e)=φ`. The degreewise monic
comparison makes this factorization unique. -/
@[reassoc (attr := simp)]
lemma liftTruncLE'_truncLE'ToRestriction :
    liftTruncLE' φ hφ ≫ K.truncLE'ToRestriction e = φ := by
  ext i
  exact liftTruncLE'.f_comp φ hφ i

section Homology

variable [HasZeroObject C]

/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. Suppose `C` has a zero object. For a complex map `φ : K → L`, with homology of `L` in
every degree, the isomorphisms between the full good truncations
and the zero extensions of `τ_eK,τ_eL` commute with the two
truncation maps. -/
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

/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. Suppose `C` has a zero object. For every source index `i`, including boundary indices,
the canonical homology comparison is `H_i(τ_eK) ≅ H_(e(i))(K)`. -/
noncomputable def truncLE'HomologyIso (i : ι) :
    (K.truncLE' e).homology i ≅ K.homology (e.f i) :=
  ((K.truncLE' e).extendHomologyIso e (j := i) rfl).symm ≪≫
    homologyMapIso (K.truncLEIso e).symm (e.f i) ≪≫
      asIso (homologyMap (K.ιTruncLE e) (e.f i))

variable {K e}

/-- Let `C` be a category with zero morphisms, `e : c → c′` a
complex-shape embedding of truncation type `IsTruncLE`, and `K` a
`c′`-shaped complex with homology in every degree. Suppose `C` has a zero object. For `φ : K → L`, with homology of `L` in every degree,
the comparisons `H_i(τ_eK) ≅ H_(e(i))(K)` commute with the
homology maps of the truncated and original complex maps. -/
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

/-- For the complex-shape embedding `n ↦ -n` from `down ℕ` into
`up ℤ`, a natural degree is a truncation boundary if and only if
it is zero. -/
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

/-- Let `C` be a category with zero morphisms and `K` an integer
cochain complex with homology in every degree. Let `τK` be its
nonnegative chain truncation along `n ↦ -n`. The degree-`n` comparison `τK_n → K^(-n)` is an
isomorphism for `n>0` and the cycle inclusion `Z⁰K → K⁰` for `n=0`. -/
noncomputable def truncLE'ToX (n : ℕ) : (K.truncLE' embeddingDownNat).X n ⟶ K.X (-n) :=
  (K.truncLE'ToRestriction embeddingDownNat).f n ≫
    (K.restrictionXIso embeddingDownNat (embeddingDownNat_f n)).hom

/-- Let `C` be a category with zero morphisms and `K` an integer
cochain complex with homology in every degree. Let `τK` be its
nonnegative chain truncation along `n ↦ -n`. The inclusion `τK_n → K^(-n)` is the good-truncation
comparison into the restricted complex followed by its degree-`n`
coordinate identification with `K^(-n)`. -/
lemma truncLE'ToX_def (n : ℕ) :
    K.truncLE'ToX n = (K.truncLE'ToRestriction embeddingDownNat).f n ≫
      (K.restrictionXIso embeddingDownNat (embeddingDownNat_f n)).hom := (rfl)

instance (n : ℕ) : Mono (K.truncLE'ToX n) := by
  rw [truncLE'ToX_def]
  infer_instance

/-- Let `C` be a category with zero morphisms and `K` an integer
cochain complex with homology in every degree. Let `τK` be its
nonnegative chain truncation along `n ↦ -n`. The inclusions satisfy
`t_(n+1) ≫ d_K^(-(n+1),-n) = d_τ^(n+1,n) ≫ t_n` for every `n`. -/
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

/-- Let `C` be a category with zero morphisms and `K` an integer
cochain complex with homology in every degree. Let `τK` be its
nonnegative chain truncation along `n ↦ -n`. The degree-zero inclusion `Z⁰K → K⁰` is killed by every
outgoing differential `K⁰ → K^j`. -/
@[reassoc]
lemma truncLE'ToX_zero_d (j : ℤ) : K.truncLE'ToX 0 ≫ K.d (-((0 : ℕ) : ℤ)) j = 0 := by
  rw [truncLE'ToX, Category.assoc]
  exact K.truncLE'ToRestriction_f_comp_d _ _ ((boundaryLE_embeddingDownNat_iff 0).2 rfl) j

variable {K} in
/-- Let `C` be a category with zero morphisms and `K` an integer
cochain complex with homology in every degree. Let `τK` be its
nonnegative chain truncation along `n ↦ -n`. For an integer cochain map `f : K → L`, with homology
of `L` in every degree, the truncated map and inclusions satisfy
`(τf)_n ≫ t_L,n = t_K,n ≫ f^(-n)`. -/
@[reassoc (attr := simp)]
lemma truncLE'Map_f_truncLE'ToX {L : CochainComplex C ℤ} [∀ i, L.HasHomology i] (f : K ⟶ L)
    (n : ℕ) :
    (truncLE'Map f embeddingDownNat).f n ≫ L.truncLE'ToX n = K.truncLE'ToX n ≫ f.f (-n) := by
  have := congr_arg (fun g => g.f n) (truncLE'ToRestriction_naturality f embeddingDownNat)
  simp only [comp_f, restrictionMap_f' f embeddingDownNat (embeddingDownNat_f n)] at this
  simp [truncLE'ToX, reassoc_of% this]

end CochainComplex
