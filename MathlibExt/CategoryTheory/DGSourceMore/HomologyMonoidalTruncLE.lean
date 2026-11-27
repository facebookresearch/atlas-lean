/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/Monoidal/TruncLE.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import MathlibExt.CategoryTheory.DGSourceMore.HomologyEmbeddingTruncLE
public import MathlibExt.CategoryTheory.DGSource.CochainTensorSummands
public import MathlibExt.CategoryTheory.DGSource.CochainTensorDifferential

/-!
# The good truncation is lax monoidal

The good truncation `τ_{≥ 0}` sends a cochain complex `K` of `R`-modules indexed by `ℤ` to the
chain complex indexed by `ℕ` with `K^{-n}` in degree `n > 0` and the cycles `Z⁰ K` in degree `0`;
in Mathlib it is the canonical truncation `K.truncLE' ComplexShape.embeddingDownNat`, the functor
`ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat R)`.  This file makes that functor lax
monoidal for the tensor products of complexes of `HomologicalComplex.monoidalCategory` on both
sides.

The tensorator `τ_{≥ 0} K ⊗ τ_{≥ 0} L ⟶ τ_{≥ 0} (K ⊗ L)` is the inclusion of the summands
`(τ_{≥ 0} K)_p ⊗ (τ_{≥ 0} L)_q ⟶ K^{-p} ⊗ L^{-q}` into `(K ⊗ L)^{-(p + q)}`.  It is a chain map
because the cycles in degree `0` are killed by the differential, and its degree-`0` component
lands in the cycles of `K ⊗ L` by the Leibniz rule; the Koszul signs `(-1)^p` of the two tensor
products agree since `(-1)^{-p} = (-1)^p`.  The unit is the identity of `R` in degree `0`.

Composed with the lax monoidal Dold–Kan functor and the forgetful functor to simplicial sets, this
turns a differential graded category into a simplicially enriched category whose mapping simplicial
sets are `DK(τ_{≥ 0} Hom(x, y))` (Lurie, *Higher Algebra*, Construction 1.3.1.13).

## Main definitions and results

* `CochainComplex.tensorTruncLE'ToRestriction`: the chain map
  `τ_{≥ 0} K ⊗ τ_{≥ 0} L ⟶ (K ⊗ L).restriction embeddingDownNat` on summands.
* `CochainComplex.truncLE'TensorHom`: the tensorator `τ_{≥ 0} K ⊗ τ_{≥ 0} L ⟶ τ_{≥ 0} (K ⊗ L)`.
* `CochainComplex.truncLE'Unit`: the unit `𝟙_ ⟶ τ_{≥ 0} 𝟙_`.
* The instance `(ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat R)).LaxMonoidal`.

## Implementation notes

The coefficients are `R`-modules, as for `HomologicalComplex.ι_tensorObj_d`: the tensor product of
cochain complexes indexed by `ℤ` needs countable coproducts commuting with the tensor product,
which `ModuleCat R` provides; these are also the coefficients of a differential graded category.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13.
* C. Weibel, *An introduction to homological algebra*, §1.2.7, for the good truncation.
-/

public section

open CategoryTheory Limits MonoidalCategory HomologicalComplex ComplexShape

universe v

namespace CochainComplex

variable {R : Type v} [CommRing R] (K L : CochainComplex (ModuleCat.{v} R) ℤ)

/-- The degree-`n` component of `CochainComplex.tensorTruncLE'ToRestriction`: on the summand
`(τ_{≥ 0} K)_p ⊗ (τ_{≥ 0} L)_q` it is the tensor product of the inclusions into `K^{-p}` and
`L^{-q}`, followed by the inclusion of `K^{-p} ⊗ L^{-q}` into `(K ⊗ L)^{-n}`. -/
noncomputable def tensorTruncLE'ToRestrictionX (n : ℕ) :
    (K.truncLE' embeddingDownNat ⊗ L.truncLE' embeddingDownNat).X n ⟶
      ((K ⊗ L).restriction embeddingDownNat).X n :=
  mapBifunctorDesc (fun p q h =>
    (K.truncLE'ToX p ⊗ₘ L.truncLE'ToX q) ≫ ιTensorObj K L (-p) (-q) (-n) (by simp at h; omega) ≫
      ((K ⊗ L).restrictionXIso embeddingDownNat (embeddingDownNat_f n)).inv)

variable {K L} in
/-- `CochainComplex.tensorTruncLE'ToRestrictionX` on the summand of bidegree `(p, q)`. -/
@[reassoc (attr := simp)]
lemma ι_tensorTruncLE'ToRestrictionX (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (K.truncLE' embeddingDownNat) (L.truncLE' embeddingDownNat) p q n h ≫
        tensorTruncLE'ToRestrictionX K L n =
      (K.truncLE'ToX p ⊗ₘ L.truncLE'ToX q) ≫ ιTensorObj K L (-p) (-q) (-n) (by omega) ≫
        ((K ⊗ L).restrictionXIso embeddingDownNat (embeddingDownNat_f n)).inv :=
  ι_mapBifunctorDesc _ _ _ _

/- The components `tensorTruncLE'ToRestrictionX` commute with the differentials.  On a summand
of bidegree `(p, q)`, each part of the differential of `τ_{≥ 0} K ⊗ τ_{≥ 0} L` matches the
corresponding part of the differential of `K ⊗ L`, except that the part differentiating a factor
of degree `0` is zero on both sides: in `τ_{≥ 0}` there is no degree `-1`, and in `K ⊗ L` it
differentiates a cycle. -/
private lemma tensorTruncLE'ToRestrictionX_comm (j : ℕ) :
    tensorTruncLE'ToRestrictionX K L (j + 1) ≫ ((K ⊗ L).restriction embeddingDownNat).d (j + 1) j =
      (K.truncLE' embeddingDownNat ⊗ L.truncLE' embeddingDownNat).d (j + 1) j ≫
        tensorTruncLE'ToRestrictionX K L j := by
  refine mapBifunctor.hom_ext (fun p q h => ?_)
  have h' : p + q = j + 1 := h
  rw [ι_tensorTruncLE'ToRestrictionX_assoc, restriction_d_eq _ embeddingDownNat
    (embeddingDownNat_f (j + 1)) (embeddingDownNat_f j)]
  simp only [Iso.inv_hom_id_assoc]
  -- The differential of a tensor product of chain complexes is the sum of its two parts.
  have hd : (K.truncLE' embeddingDownNat ⊗ L.truncLE' embeddingDownNat).d (j + 1) j =
      mapBifunctor.D₁ _ _ (curriedTensor (ModuleCat.{v} R)) (down ℕ) (j + 1) j +
        mapBifunctor.D₂ _ _ (curriedTensor (ModuleCat.{v} R)) (down ℕ) (j + 1) j :=
    mapBifunctor.d_eq _ _ _ _ _ _
  rw [hd, Preadditive.add_comp, Preadditive.comp_add]
  -- Expand both differentials on the summand; the bidegree `(0, 0)` does not occur.
  obtain _ | r := p <;> obtain _ | s := q
  · omega
  on_goal 1 =>
    obtain rfl : s = j := by omega
    rw [ι_tensorObj_d'_assoc K L (p := -((0 : ℕ) : ℤ)) (q := -((s + 1 : ℕ) : ℤ))
      (j := -((s + 1 : ℕ) : ℤ)) (p' := -((0 : ℕ) : ℤ) + 1) (q' := -(s : ℤ)) (j' := -(s : ℤ))
      (by omega) rfl (by omega) (by omega),
      ChainComplex.ιTensorObj_D₁_zero_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc]
  on_goal 2 =>
    obtain rfl : r = j := by omega
    rw [ι_tensorObj_d'_assoc K L (p := -((r + 1 : ℕ) : ℤ)) (q := -((0 : ℕ) : ℤ))
      (j := -((r + 1 : ℕ) : ℤ)) (p' := -(r : ℤ)) (q' := -((0 : ℕ) : ℤ) + 1) (j' := -(r : ℤ))
      (by omega) (by omega) rfl (by omega),
      ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_zero_assoc]
  on_goal 3 =>
    rw [ι_tensorObj_d'_assoc K L (p := -((r + 1 : ℕ) : ℤ)) (q := -((s + 1 : ℕ) : ℤ))
      (j := -((j + 1 : ℕ) : ℤ)) (p' := -(r : ℤ)) (q' := -(s : ℤ)) (j' := -(j : ℤ)) (by omega)
      (by omega) (by omega) (by omega),
      ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc]
  -- Match the parts of the two differentials, using that degree `0` of `τ_{≥ 0}` is cycles.
  all_goals
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc, Linear.smul_comp,
      Linear.comp_smul, ι_tensorTruncLE'ToRestrictionX, tensorHom_comp_whiskerRight_assoc,
      tensorHom_comp_whiskerLeft_assoc, whiskerRight_comp_tensorHom_assoc,
      whiskerLeft_comp_tensorHom_assoc, truncLE'ToX_d_succ, truncLE'ToX_zero_d,
      Int.negOnePow_neg, Units.smul_def, Int.coe_negOnePow_natCast,
      MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero, zero_comp, smul_zero,
      zero_add, add_zero]

/-- The chain map `τ_{≥ 0} K ⊗ τ_{≥ 0} L ⟶ (K ⊗ L).restriction embeddingDownNat` given on the
summand `(τ_{≥ 0} K)_p ⊗ (τ_{≥ 0} L)_q` by the inclusion into `K^{-p} ⊗ L^{-q}`; it factors through
the good truncation `τ_{≥ 0} (K ⊗ L)` as `CochainComplex.truncLE'TensorHom`. -/
noncomputable def tensorTruncLE'ToRestriction :
    K.truncLE' embeddingDownNat ⊗ L.truncLE' embeddingDownNat ⟶
      (K ⊗ L).restriction embeddingDownNat where
  f := tensorTruncLE'ToRestrictionX K L
  comm' i j hij := by
    obtain rfl : i = j + 1 := by simpa using hij.symm
    exact tensorTruncLE'ToRestrictionX_comm K L j

/-- The components of `CochainComplex.tensorTruncLE'ToRestriction`. -/
@[simp]
lemma tensorTruncLE'ToRestriction_f (n : ℕ) :
    (tensorTruncLE'ToRestriction K L).f n = tensorTruncLE'ToRestrictionX K L n :=
  (rfl)

/-- The degree-`0` component of `CochainComplex.tensorTruncLE'ToRestriction` lands in the cycles
of `K ⊗ L`: it is killed by the differential, by the Leibniz rule. -/
lemma tensorTruncLE'ToRestriction_f_zero_comp_d (i' : ℤ) (hi' : embeddingDownNat.f 0 = i')
    (j' : ℤ) :
    (tensorTruncLE'ToRestriction K L).f 0 ≫
      ((K ⊗ L).restrictionXIso embeddingDownNat hi').hom ≫ (K ⊗ L).d i' j' = 0 := by
  obtain rfl : i' = -((0 : ℕ) : ℤ) := by simpa using hi'.symm
  refine mapBifunctor.hom_ext (fun p q h => ?_)
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by
    have h' : p + q = 0 := h
    omega
  rw [comp_zero, tensorTruncLE'ToRestriction_f, ι_tensorTruncLE'ToRestrictionX_assoc,
    Iso.inv_hom_id_assoc]
  by_cases hj : -((0 : ℕ) : ℤ) + 1 = j'
  · rw [ι_tensorObj_d' K L (p := -((0 : ℕ) : ℤ)) (q := -((0 : ℕ) : ℤ)) (j := -((0 : ℕ) : ℤ))
      (p' := -((0 : ℕ) : ℤ) + 1) (q' := -((0 : ℕ) : ℤ) + 1) (j' := j') (by omega) rfl rfl hj]
    simp only [Preadditive.comp_add, Linear.comp_units_smul, tensorHom_comp_whiskerRight_assoc,
      tensorHom_comp_whiskerLeft_assoc, truncLE'ToX_zero_d, MonoidalPreadditive.zero_tensor,
      MonoidalPreadditive.tensor_zero, zero_comp, smul_zero, add_zero]
  · rw [(K ⊗ L).shape _ _ (by simpa using hj), comp_zero, comp_zero]

/-- The tensorator of the good truncation, `τ_{≥ 0} K ⊗ τ_{≥ 0} L ⟶ τ_{≥ 0} (K ⊗ L)`: the
factorization of `CochainComplex.tensorTruncLE'ToRestriction` through `τ_{≥ 0} (K ⊗ L)`. -/
noncomputable def truncLE'TensorHom :
    K.truncLE' embeddingDownNat ⊗ L.truncLE' embeddingDownNat ⟶
      (K ⊗ L).truncLE' embeddingDownNat :=
  liftTruncLE' (tensorTruncLE'ToRestriction K L) (fun i hi i' hi' j' => by
    obtain rfl := (boundaryLE_embeddingDownNat_iff i).1 hi
    exact tensorTruncLE'ToRestriction_f_zero_comp_d K L i' hi' j')

/-- The tensorator of the good truncation, followed by the inclusion of `τ_{≥ 0} (K ⊗ L)` into the
restriction of `K ⊗ L`, is `CochainComplex.tensorTruncLE'ToRestriction`. -/
@[reassoc (attr := simp)]
lemma truncLE'TensorHom_truncLE'ToRestriction :
    truncLE'TensorHom K L ≫ (K ⊗ L).truncLE'ToRestriction embeddingDownNat =
      tensorTruncLE'ToRestriction K L :=
  liftTruncLE'_truncLE'ToRestriction _ _

variable {K L} in
/-- On the summand `(τ_{≥ 0} K)_p ⊗ (τ_{≥ 0} L)_q`, the tensorator of the good truncation is the
tensor product of the inclusions into `K^{-p}` and `L^{-q}`. -/
@[reassoc (attr := simp)]
lemma ι_truncLE'TensorHom_f_truncLE'ToX (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (K.truncLE' embeddingDownNat) (L.truncLE' embeddingDownNat) p q n h ≫
        (truncLE'TensorHom K L).f n ≫ (K ⊗ L).truncLE'ToX n =
      (K.truncLE'ToX p ⊗ₘ L.truncLE'ToX q) ≫ ιTensorObj K L (-p) (-q) (-n) (by omega) := by
  have := congr_arg (fun g => g.f n) (truncLE'TensorHom_truncLE'ToRestriction K L)
  simp only [comp_f] at this
  simp [truncLE'ToX_def, reassoc_of% this]

variable (R) in
/-- The unit of the good truncation, `𝟙_ ⟶ τ_{≥ 0} 𝟙_`: the identity of `R`, viewed as a cycle in
degree `0` of the unit complex. -/
noncomputable def truncLE'Unit :
    𝟙_ (ChainComplex (ModuleCat.{v} R) ℕ) ⟶
      (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).truncLE' embeddingDownNat :=
  liftTruncLE'
    (mkHomFromSingle ((singleObjXIsoOfEq (up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) (-((0 : ℕ) : ℤ))
      (by simp)).inv ≫ ((𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).restrictionXIso embeddingDownNat
        (embeddingDownNat_f 0)).inv) (fun k hk => by simp at hk))
    (fun i _ i' hi' j' => by
      -- The unit complex is a single complex, whose differentials vanish.
      have hd : (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).d i' j' = 0 := single_obj_d _ _ _ _ _
      rw [hd, comp_zero, comp_zero])

variable (R) in
/-- In degree `0`, the unit of the good truncation is the identity of `R`, up to the canonical
isomorphisms with the degree-`0` terms of the two unit complexes. -/
@[reassoc (attr := simp)]
lemma truncLE'Unit_f_truncLE'ToX :
    (truncLE'Unit R).f 0 ≫ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).truncLE'ToX 0 =
      (singleObjXSelf (down ℕ) 0 (𝟙_ (ModuleCat.{v} R))).hom ≫
        (singleObjXIsoOfEq (up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) (-((0 : ℕ) : ℤ)) (by simp)).inv := by
  rw [truncLE'ToX_def, ← Category.assoc, ← comp_f, truncLE'Unit, liftTruncLE'_truncLE'ToRestriction,
    mkHomFromSingle_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {K L} in
private lemma truncLE'TensorHom_naturality {K' L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    (truncLE'Map f embeddingDownNat ⊗ₘ truncLE'Map g embeddingDownNat) ≫ truncLE'TensorHom K' L' =
      truncLE'TensorHom K L ≫ truncLE'Map (f ⊗ₘ g) embeddingDownNat := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [← cancel_mono ((K' ⊗ L').truncLE'ToX n)]
  refine mapBifunctor.hom_ext (fun p q h => ?_)
  simp only [comp_f, Category.assoc, truncLE'Map_f_truncLE'ToX, tensorHom_eq_mapBifunctorMap]
  rw [ι_tensorHom_assoc, ι_truncLE'TensorHom_f_truncLE'ToX, ι_truncLE'TensorHom_f_truncLE'ToX_assoc,
    ι_tensorHom, tensorHom_comp_tensorHom_assoc, truncLE'Map_f_truncLE'ToX,
    truncLE'Map_f_truncLE'ToX, tensorHom_comp_tensorHom_assoc]

private lemma truncLE'TensorHom_assoc (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    (truncLE'TensorHom K L ▷ M.truncLE' embeddingDownNat) ≫ truncLE'TensorHom (K ⊗ L) M ≫
        truncLE'Map (α_ K L M).hom embeddingDownNat =
      (α_ _ _ _).hom ≫ (K.truncLE' embeddingDownNat ◁ truncLE'TensorHom L M) ≫
        truncLE'TensorHom K (L ⊗ M) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [← cancel_mono ((K ⊗ (L ⊗ M)).truncLE'ToX n)]
  refine mapBifunctor₁₂.hom_ext (fun p q r h => ?_)
  have h' : p + q + r = n := h
  rw [mapBifunctor₁₂.ι_eq_whiskerRight _ _ _ p q r (p + q) n rfl h']
  simp only [comp_f, Category.assoc, truncLE'Map_f_truncLE'ToX, ι_whiskerRight_assoc,
    ι_truncLE'TensorHom_f_truncLE'ToX_assoc, whiskerRight_comp_tensorHom_assoc,
    ι_truncLE'TensorHom_f_truncLE'ToX,
    ι_ι_associator_hom_assoc _ _ _ p q r (p + q) (q + r) n rfl rfl h' (by omega),
    ι_whiskerLeft_assoc, whiskerLeft_comp_tensorHom_assoc]
  rw [← tensorHom_comp_whiskerRight_assoc, ← tensorHom_comp_whiskerLeft_assoc,
    ι_ι_associator_hom K L M (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((q + r : ℕ) : ℤ)) (-(n : ℤ)) (by omega) (by omega) (by omega) (by omega),
    associator_naturality_assoc]

omit L in
private lemma singleObjXIsoOfEq_inv_whiskerRight_ι {i : ℤ} (hi : i = 0) (q j : ℤ)
    (h : i + q = j) :
    ((singleObjXIsoOfEq (up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) i hi).inv ▷ K.X q) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K i q j h =
      ((singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv ▷ K.X q) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K 0 q j (by omega) := by
  subst hi
  rfl

omit L in
private lemma whiskerLeft_singleObjXIsoOfEq_inv_ι {i : ℤ} (hi : i = 0) (p j : ℤ)
    (h : p + i = j) :
    (K.X p ◁ (singleObjXIsoOfEq (up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) i hi).inv) ≫
        ιTensorObj K (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) p i j h =
      (K.X p ◁ (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv) ≫
        ιTensorObj K (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) p 0 j (by omega) := by
  subst hi
  rfl

omit L in
private lemma leftUnitor_inv_truncLE'Unit_truncLE'TensorHom :
    (λ_ (K.truncLE' embeddingDownNat)).inv ≫ (truncLE'Unit R ▷ K.truncLE' embeddingDownNat) ≫
        truncLE'TensorHom (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K =
      truncLE'Map (λ_ K).inv embeddingDownNat := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [← cancel_mono ((𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⊗ K).truncLE'ToX n)]
  simp only [comp_f, Category.assoc, truncLE'Map_f_truncLE'ToX, leftUnitor_inv_f, leftUnitor'_inv,
    ι_whiskerRight_assoc, ι_truncLE'TensorHom_f_truncLE'ToX, whiskerRight_comp_tensorHom_assoc,
    truncLE'Unit_f_truncLE'ToX, Iso.inv_hom_id_assoc, leftUnitor_inv_comp_tensorHom_assoc,
    singleObjXIsoOfEq_inv_whiskerRight_ι]
  -- Mathlib states `leftUnitor'_inv` with `tensorUnit`, the definition of `𝟙_`.
  rfl

omit L in
private lemma rightUnitor_inv_truncLE'Unit_truncLE'TensorHom :
    (ρ_ (K.truncLE' embeddingDownNat)).inv ≫ (K.truncLE' embeddingDownNat ◁ truncLE'Unit R) ≫
        truncLE'TensorHom K (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) =
      truncLE'Map (ρ_ K).inv embeddingDownNat := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [← cancel_mono ((K ⊗ 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).truncLE'ToX n)]
  simp only [comp_f, Category.assoc, truncLE'Map_f_truncLE'ToX, rightUnitor_inv_f,
    rightUnitor'_inv, ι_whiskerLeft_assoc, ι_truncLE'TensorHom_f_truncLE'ToX,
    whiskerLeft_comp_tensorHom_assoc, truncLE'Unit_f_truncLE'ToX, Iso.inv_hom_id_assoc,
    rightUnitor_inv_comp_tensorHom_assoc, whiskerLeft_singleObjXIsoOfEq_inv_ι]
  -- Mathlib states `rightUnitor'_inv` with `tensorUnit`, the definition of `𝟙_`.
  rfl

variable (R) in
/-- The good truncation `τ_{≥ 0}` from cochain complexes of `R`-modules indexed by `ℤ` to chain
complexes indexed by `ℕ` is lax monoidal, with unit `CochainComplex.truncLE'Unit` and tensorator
`CochainComplex.truncLE'TensorHom`. -/
noncomputable instance truncLE'FunctorLaxMonoidal :
    (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)).LaxMonoidal where
  ε := truncLE'Unit R
  μ := truncLE'TensorHom
  μ_natural_left f K := by
    have h := truncLE'TensorHom_naturality f (𝟙 K)
    rw [truncLE'Map_id, tensorHom_id, tensorHom_id] at h
    exact h
  μ_natural_right K f := by
    have h := truncLE'TensorHom_naturality (𝟙 K) f
    rw [truncLE'Map_id, id_tensorHom, id_tensorHom] at h
    exact h
  associativity K L M := by exact truncLE'TensorHom_assoc K L M
  left_unitality K := by
    have h : (λ_ (K.truncLE' embeddingDownNat)).inv ≫
        (truncLE'Unit R ▷ K.truncLE' embeddingDownNat) ≫
          truncLE'TensorHom (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K ≫
            truncLE'Map (λ_ K).hom embeddingDownNat = 𝟙 _ := by
      rw [reassoc_of% leftUnitor_inv_truncLE'Unit_truncLE'TensorHom, ← truncLE'Map_comp,
        Iso.inv_hom_id, truncLE'Map_id]
    exact (((Iso.inv_comp_eq _).1 h).trans (Category.comp_id _)).symm
  right_unitality K := by
    have h : (ρ_ (K.truncLE' embeddingDownNat)).inv ≫
        (K.truncLE' embeddingDownNat ◁ truncLE'Unit R) ≫
          truncLE'TensorHom K (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) ≫
            truncLE'Map (ρ_ K).hom embeddingDownNat = 𝟙 _ := by
      rw [reassoc_of% rightUnitor_inv_truncLE'Unit_truncLE'TensorHom, ← truncLE'Map_comp,
        Iso.inv_hom_id, truncLE'Map_id]
    exact (((Iso.inv_comp_eq _).1 h).trans (Category.comp_id _)).symm

variable (R) in
/-- The unit of the lax monoidal good truncation is `CochainComplex.truncLE'Unit`. -/
@[simp]
lemma truncLE'Functor_ε :
    Functor.LaxMonoidal.ε (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)) = truncLE'Unit R :=
  (rfl)

/-- The tensorator of the lax monoidal good truncation is `CochainComplex.truncLE'TensorHom`. -/
@[simp]
lemma truncLE'Functor_μ :
    Functor.LaxMonoidal.μ (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)) K L =
      truncLE'TensorHom K L :=
  (rfl)

end CochainComplex
