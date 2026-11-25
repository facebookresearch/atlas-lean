/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/ShiftClosure/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: module/namespace paths are adapted for Atlas, and the
universes of the final independent section are redeclared explicitly.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import MathlibExt.CategoryTheory.DGSource.DGFunctor
public import MathlibExt.CategoryTheory.DGSource.DGFunctorHomComplex

/-!
# The shift closure of a differential graded category

For a differential graded category `C`, the shift closure `MathlibExt.DGSource.DGShiftClosure C` adjoins a
formal shift `X[r]` of every object `X` by every integer `r`.  Its Hom complexes are shifts of
those of `C`:

`Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`,

with Mathlib's cochain-shift convention `K[a]^p = K^(p + a)` and differential `(-1)^a d_K`.  So a
morphism `X[r] ⟶ Y[s]` of degree `p` is a morphism `X ⟶ Y` of degree `p + s - r`
(`MathlibExt.DGSource.DGShiftClosure.dgHomEquiv`), and the differential of the shift closure is
`(-1)^(s - r)` times the differential of `C`.

Composition carries a sign.  In Mathlib's enriched factor order, a degree-`p` morphism
`f : X[r] ⟶ Y[s]` followed by `g : Y[s] ⟶ Z[t]` composes to
`(-1)^((t - s) * (p + s - r)) • dgComp f g`.  In Keller's order, where
`g ∘ f = (-1)^(p * q) • dgComp f g` for `g` of degree `q`, the sign becomes `(-1)^((s - r) * q)`.
These are the signs for which the formal shifts of cochain complexes are Mathlib's shifted
complexes `K⟦r⟧`, with `Hom(K, L)[s - r] ≅ Hom(K⟦r⟧, L⟦s⟧)` multiplying the underlying cochain
by `(-1)^(r * p)`: see `TauCeti/CategoryTheory/DG/ShiftClosure/CochainComplex.lean`.

Shifting every object by the same integer `n` does not change the Hom complexes, so
`X[r] ↦ X[r + n]` is a DG functor `MathlibExt.DGSource.DGShiftClosure.shiftFunctor n` which is the identity on
underlying morphisms of `C`.  The objects `X[r]` and `X[r + n]` are related by the closed
morphism `MathlibExt.DGSource.DGShiftClosure.toShift : X[r] ⟶ X[r + n]` of degree `-n` and its inverse
`MathlibExt.DGSource.DGShiftClosure.fromShift` of degree `n`, whose underlying morphisms are `(-1)^(n * r)`
times the identity of `X`.  With this sign, `toShift` is natural up to the Koszul sign:
`f ≫ toShift = (-1)^(n * p) • toShift ≫ f[n]` for `f` of degree `p`, and so is `fromShift`.

A DG functor `F : C ⥤ D` induces a DG functor `F.mapDGShiftClosure` between the shift closures,
sending `X[r]` to `(F X)[r]` and applying `F` to the underlying morphisms; it commutes with the
shifts and preserves the comparison morphisms.

The shift closure is the home of the matrix entries of one-sided twisted complexes, the objects
`(⊕ᵢ Xᵢ[rᵢ], δ)` of the pretriangulated envelope of Bondal and Kapranov.

## Main definitions

* `MathlibExt.DGSource.DGShiftClosure`: the objects `X[r]` of the shift closure.
* `MathlibExt.DGSource.DGShiftClosure.homComplexData`: its explicit Hom-complex data.
* `MathlibExt.DGSource.DGShiftClosure.dgHomEquiv`: degree-`n` morphisms `X[r] ⟶ Y[s]` are degree-`n + s - r`
  morphisms `X ⟶ Y`.
* `MathlibExt.DGSource.DGShiftClosure.ι`: the DG functor `X ↦ X[0]`.
* `MathlibExt.DGSource.DGShiftClosure.shiftFunctor`: the DG functor `X[r] ↦ X[r + n]`.
* `MathlibExt.DGSource.DGShiftClosure.toShift` and `MathlibExt.DGSource.DGShiftClosure.fromShift`: the closed comparison
  morphisms `X[r] ⟶ X[r + n]` of degree `-n` and `X[r + n] ⟶ X[r]` of degree `n`.
* `CategoryTheory.EnrichedFunctor.mapDGShiftClosure`: the DG functor `X[r] ↦ (F X)[r]` induced by
  a DG functor `F`.

## Main results

* `MathlibExt.DGSource.DGShiftClosure.dgHomEquiv_dgDifferential`: the differential is `(-1)^(s - r) d`.
* `MathlibExt.DGSource.DGShiftClosure.dgHomEquiv_dgComp`: composition carries the sign
  `(-1)^((t - s) * (p + s - r))`.
* `MathlibExt.DGSource.DGShiftClosure.dgHomEquiv_negOnePow_smul_dgComp`: in Keller's order the sign is
  `(-1)^((s - r) * q)`.
* `MathlibExt.DGSource.DGShiftClosure.dgHomEquiv_dgId`: the identity of `X[r]` is the identity of `X`.
* `MathlibExt.DGSource.DGShiftClosure.isIso_ι_map`: `X ↦ X[0]` is an isomorphism on Hom complexes.
* `MathlibExt.DGSource.DGShiftClosure.dgComp_toShift_fromShift` and
  `MathlibExt.DGSource.DGShiftClosure.dgComp_fromShift_toShift`: the comparison morphisms are mutually
  inverse.
* `MathlibExt.DGSource.DGShiftClosure.dgComp_toShift` and `MathlibExt.DGSource.DGShiftClosure.dgComp_fromShift`: the
  comparison morphisms are natural up to the Koszul sign.
* `CategoryTheory.EnrichedFunctor.mapDGShiftClosureHom_shiftHomEquiv`,
  `CategoryTheory.EnrichedFunctor.mapDGShiftClosureHom_toShift` and
  `CategoryTheory.EnrichedFunctor.mapDGShiftClosureHom_fromShift`: the DG functor induced by `F`
  commutes with shifting every object and preserves the comparison morphisms.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory HomologicalComplex

namespace MathlibExt.DGSource

universe v u

/-- The objects of the **shift closure** of a differential graded category on the objects `C`:
an object `X` of `C` together with an integer `r`, standing for the formal shift `X[r]`.  The
Hom complexes are `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`; see
`MathlibExt.DGSource.DGShiftClosure.homComplexData`. -/
@[ext]
structure DGShiftClosure (C : Type u) where
  /-- The underlying object `X` of the shifted object `X[r]`. -/
  obj : C
  /-- The shift `r` of the shifted object `X[r]`. -/
  shift : ℤ

namespace DGShiftClosure

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-! ### The Hom-complex data -/

/-- The Hom complex `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]` of the shift closure. -/
private abbrev homComplex (X Y : DGShiftClosure C) : CochainComplex (ModuleCat.{v} R) ℤ :=
  (dgHomComplex R X.obj Y.obj)⟦Y.shift - X.shift⟧

/-- The sign `(-1)^((t - s) * (p + s - r))` of the composite of a degree-`p` morphism
`X[r] ⟶ Y[s]` followed by a morphism `Y[s] ⟶ Z[t]`. -/
private abbrev compSign (X Y Z : DGShiftClosure C) (p : ℤ) : ℤˣ :=
  ((Z.shift - Y.shift) * (p + (Y.shift - X.shift))).negOnePow

/-- Composition in the shift closure: the composition of `C` on the underlying morphisms, with
the sign `MathlibExt.DGSource.DGShiftClosure.compSign`. -/
private noncomputable def comp {X Y Z : DGShiftClosure C} (p q n : ℤ) (h : p + q = n) :
    (homComplex R X Y).X p →ₗ[R] (homComplex R Y Z).X q →ₗ[R] (homComplex R X Z).X n :=
  compSign X Y Z p • TensorProduct.curry
    (dgCompMap R X.obj Y.obj Z.obj (p + (Y.shift - X.shift)) (q + (Z.shift - Y.shift))
      (n + (Z.shift - X.shift)) (by omega)).hom

private theorem comp_apply {X Y Z : DGShiftClosure C} (p q n : ℤ) (h : p + q = n)
    (f : (homComplex R X Y).X p) (g : (homComplex R Y Z).X q) :
    comp R p q n h f g = compSign X Y Z p • dgComp R (n := n + (Z.shift - X.shift))
      (p := p + (Y.shift - X.shift)) (q := q + (Z.shift - Y.shift)) f g (by omega) := by
  rw [comp, LinearMap.smul_apply, LinearMap.smul_apply, TensorProduct.curry_apply,
    dgCompMap_tmul]

/-- The **explicit Hom-complex data of the shift closure**: `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`,
whose differential is `(-1)^(s - r) d`, with composition the composition of `C` multiplied by
`(-1)^((t - s) * (p + s - r))` and identity the identity of `C`. -/
noncomputable def homComplexData : DGCategoryData R (DGShiftClosure C) where
  hom := homComplex R
  comp := comp R
  id X := castDeg R (p' := 0 + (X.shift - X.shift)) (by rw [sub_self, add_zero]) (dgId R X.obj)
  d_comp {X Y Z p q n} h f g := by
    simp only [comp_apply, CochainComplex.shiftFunctor_obj_d', ModuleCat.hom_smul,
      LinearMap.smul_apply, map_zsmul_unit]
    rw [dgHomComplex_d_dgComp R (p' := p + 1 + (Y.shift - X.shift))
      (q' := q + 1 + (Z.shift - Y.shift)) (by omega) (by omega) (by omega)]
    simp only [smul_add, smul_smul]
    congr 2 <;> simp only [compSign, ← Int.negOnePow_add] <;> rw [Int.negOnePow_eq_iff]
    · exact ⟨0, by ring⟩
    · exact ⟨Y.shift - X.shift, by ring⟩
  comp_assoc {W X Y Z p q r pq qr n} hpq hqr h f g k := by
    simp only [comp_apply, units_smul_dgComp, dgComp_units_smul, smul_smul]
    rw [dgComp_assoc R (p := p + (X.shift - W.shift)) (q := q + (Y.shift - X.shift))
      (r := r + (Z.shift - Y.shift)) (pq := pq + (Y.shift - W.shift))
      (qr := qr + (Z.shift - X.shift)) f g k (by omega) (by omega) (by omega)]
    congr 1
    simp only [compSign, ← Int.negOnePow_add]
    congr 1
    subst hpq
    ring
  id_comp {X Y q} g := by
    rw [comp_apply, castDeg_dgComp R (p := 0) (q := q + (Y.shift - X.shift))
      (n := q + (Y.shift - X.shift)) (by rw [sub_self, add_zero]) rfl, dgId_dgComp, castDeg_self]
    simp [compSign]
  comp_id {X Y p} f := by
    rw [comp_apply, dgComp_castDeg R (p := p + (Y.shift - X.shift)) (q := 0)
      (n := p + (Y.shift - X.shift)) (by rw [sub_self, add_zero]) rfl, dgComp_dgId, castDeg_self]
    simp [compSign]

/-- The **shift closure** of a differential graded category: the objects `X[r]`, with Hom
complexes `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`. -/
noncomputable instance : DGCategory R (DGShiftClosure C) :=
  (homComplexData R).toDGCategory

/-! ### Morphisms, differential, composition and identity -/

/-- The Hom complex `Hom(X[r], Y[s])` of the shift closure is the shifted Hom complex
`Hom(X, Y)[s - r]`. -/
theorem dgHomComplex_eq (X Y : DGShiftClosure C) :
    dgHomComplex R X Y = (dgHomComplex R X.obj Y.obj)⟦Y.shift - X.shift⟧ :=
  (rfl)

/-- A morphism `X[r] ⟶ Y[s]` of degree `n` in the shift closure is a morphism `X ⟶ Y` of degree
`n + (s - r)` in `C`. -/
noncomputable def dgHomEquiv (X Y : DGShiftClosure C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R (n + (Y.shift - X.shift)) X.obj Y.obj :=
  LinearEquiv.refl R _

/-- The differential of the shift closure is `(-1)^(s - r)` times the differential of `C`. -/
@[simp↓]
theorem dgHomEquiv_dgDifferential {X Y : DGShiftClosure C} (n : ℤ) (f : DGHom R n X Y) :
    dgHomEquiv R X Y (n + 1) (dgDifferential R n f) =
      (Y.shift - X.shift).negOnePow • ((dgHomComplex R X.obj Y.obj).d (n + (Y.shift - X.shift))
        (n + 1 + (Y.shift - X.shift))).hom (dgHomEquiv R X Y n f) := by
  refine ((homComplexData R).dgDifferential_toDGCategory n f).trans ?_
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (CochainComplex.shiftFunctor_obj_d' (dgHomComplex R X.obj Y.obj) (Y.shift - X.shift) n
      (n + 1))) f

/-- Composition in the shift closure: a degree-`p` morphism `f : X[r] ⟶ Y[s]` followed by
`g : Y[s] ⟶ Z[t]` is the composite of the underlying morphisms of `C`, with the sign
`(-1)^((t - s) * (p + s - r))`. -/
@[simp↓]
theorem dgHomEquiv_dgComp {X Y Z : DGShiftClosure C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    dgHomEquiv R X Z n (dgComp R f g h) =
      ((Z.shift - Y.shift) * (p + (Y.shift - X.shift))).negOnePow •
        dgComp R (dgHomEquiv R X Y p f) (dgHomEquiv R Y Z q g) (by omega) :=
  ((homComplexData R).dgComp_toDGCategory f g h).trans (comp_apply R p q n h f g)

/-- **The shift-closure composition sign in Keller's order**: for `f : X[r] ⟶ Y[s]` of degree
`p` and `g : Y[s] ⟶ Z[t]` of degree `q`, the Keller-ordered composite
`g ∘ f = (-1)^(p * q) • dgComp f g` is the Keller-ordered composite of the underlying morphisms
of `C`, of degrees `p + s - r` and `q + t - s`, multiplied by `(-1)^((s - r) * q)`. -/
theorem dgHomEquiv_negOnePow_smul_dgComp {X Y Z : DGShiftClosure C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    dgHomEquiv R X Z n ((p * q).negOnePow • dgComp R f g h) =
      ((Y.shift - X.shift) * q).negOnePow •
        ((p + (Y.shift - X.shift)) * (q + (Z.shift - Y.shift))).negOnePow •
          dgComp R (dgHomEquiv R X Y p f) (dgHomEquiv R Y Z q g) (by omega) := by
  rw [map_zsmul_unit, dgHomEquiv_dgComp, smul_smul, smul_smul, ← Int.negOnePow_add,
    ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨-((Y.shift - X.shift) * q), by ring⟩

/-- The identity of `X[r]` in the shift closure is the identity of `X`. -/
@[simp↓]
theorem dgHomEquiv_dgId (X : DGShiftClosure C) :
    dgHomEquiv R X X 0 (dgId R X) =
      ((dgHomComplex R X.obj X.obj).XIsoOfEq (by rw [sub_self, add_zero])).hom (dgId R X.obj) :=
  ((homComplexData R).dgId_toDGCategory X).trans (LinearMap.congr_fun (castDeg_def R _) _)

/-! ### The inclusion `X ↦ X[0]` -/

/-- The action of the inclusion `X ↦ X[0]` on morphisms of degree `n`: a degree-`n` morphism
`X ⟶ Y` of `C` is a degree-`n` morphism `X[0] ⟶ Y[0]` of the shift closure. -/
noncomputable def ιHomEquiv (X Y : C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n (⟨X, 0⟩ : DGShiftClosure C) ⟨Y, 0⟩ :=
  ((dgHomComplex R X Y).XIsoOfEq (by rw [sub_self, add_zero])).toLinearEquiv.trans
    (dgHomEquiv R ⟨X, 0⟩ ⟨Y, 0⟩ n).symm

/-- The inclusion `X ↦ X[0]` does not change the underlying morphism. -/
@[simp]
theorem dgHomEquiv_ιHomEquiv {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    dgHomEquiv R ⟨X, 0⟩ ⟨Y, 0⟩ n (ιHomEquiv R X Y n f) =
      ((dgHomComplex R X Y).XIsoOfEq (by rw [sub_self, add_zero])).hom f := by
  simp [ιHomEquiv]

/-- The DG functor `X ↦ X[0]` from a differential graded category to its shift closure. -/
-- The body is exposed so that `(ι R).obj X` is definitionally `⟨X, 0⟩`, as for
-- `CategoryTheory.EnrichedFunctor.ofDGMap`.
@[expose]
noncomputable def ι : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C (DGShiftClosure C) :=
  EnrichedFunctor.ofDGMap (fun X ↦ ⟨X, 0⟩) (fun {X Y} n ↦ (ιHomEquiv R X Y n).toLinearMap)
    (fun {X Y} n f ↦ (dgHomEquiv R _ _ (n + 1)).injective <| by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, dgHomEquiv_dgDifferential,
        dgHomEquiv_ιHomEquiv, dgHomEquiv_ιHomEquiv]
      simp only [sub_self, Int.negOnePow_zero, one_smul]
      simp only [← castDeg_def]
      exact (d_castDeg R _ _ f).symm)
    (fun X ↦ (dgHomEquiv R _ _ 0).injective <| by
      rw [LinearEquiv.coe_coe, dgHomEquiv_ιHomEquiv, dgHomEquiv_dgId])
    (fun {X Y Z p q n} f g h ↦ (dgHomEquiv R _ _ n).injective <| by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.coe_coe, dgHomEquiv_dgComp,
        dgHomEquiv_ιHomEquiv, dgHomEquiv_ιHomEquiv, dgHomEquiv_ιHomEquiv]
      simp only [sub_self, zero_mul, Int.negOnePow_zero, one_smul]
      simp only [← castDeg_def]
      exact ((castDeg_dgComp R _ (by rw [sub_self, add_zero]) f _ _).trans
        (congrArg _ ((dgComp_castDeg R _ rfl f g _).trans (castDeg_self R _ _)))).symm)

/-- The inclusion sends `X` to `X[0]`. -/
@[simp]
theorem ι_obj (X : C) : (ι R).obj X = ⟨X, 0⟩ :=
  rfl

/-- The inclusion acts on morphisms by `MathlibExt.DGSource.DGShiftClosure.ιHomEquiv`. -/
theorem dgMap_ι {X Y : C} {n : ℤ} (f : DGHom R n X Y) : (ι R).dgMap n f = ιHomEquiv R X Y n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- The inclusion `X ↦ X[0]` is an isomorphism on Hom complexes: `C` is a full DG subcategory of
its shift closure. -/
instance isIso_ι_map (X Y : C) : IsIso ((ι R).map X Y) :=
  have (n : ℤ) : IsIso (((ι R).map X Y).f n) := (ιHomEquiv R X Y n).toModuleIso.isIso_hom
  HomologicalComplex.Hom.isIso_of_components _

/-! ### Shifting every object -/

/-- Shifting both objects by `n` does not change the morphisms: a degree-`p` morphism
`X[r] ⟶ Y[s]` and a degree-`p` morphism `X[r + n] ⟶ Y[s + n]` are both morphisms `X ⟶ Y` of
degree `p + (s - r)`. -/
noncomputable def shiftHomEquiv (X Y : DGShiftClosure C) (n p : ℤ) :
    DGHom R p X Y ≃ₗ[R] DGHom R p (⟨X.obj, X.shift + n⟩ : DGShiftClosure C) ⟨Y.obj, Y.shift + n⟩ :=
  ((dgHomEquiv R X Y p).trans ((dgHomComplex R X.obj Y.obj).XIsoOfEq
    (by omega : p + (Y.shift - X.shift) = p + (Y.shift + n - (X.shift + n)))).toLinearEquiv).trans
      (dgHomEquiv R ⟨X.obj, X.shift + n⟩ ⟨Y.obj, Y.shift + n⟩ p).symm

/-- Shifting both objects does not change the underlying morphism of `C`. -/
@[simp]
theorem dgHomEquiv_shiftHomEquiv {X Y : DGShiftClosure C} {n p : ℤ} (f : DGHom R p X Y) :
    dgHomEquiv R _ _ p (shiftHomEquiv R X Y n p f) =
      castDeg R (by dsimp only; omega) (dgHomEquiv R X Y p f) := by
  simp [shiftHomEquiv, castDeg_def]

/-- Shifting both objects commutes with the differential: both differentials are `(-1)^(s - r)`
times the differential of `C`. -/
theorem shiftHomEquiv_dgDifferential {X Y : DGShiftClosure C} (n p : ℤ) (f : DGHom R p X Y) :
    shiftHomEquiv R X Y n (p + 1) (dgDifferential R p f) =
      dgDifferential R p (shiftHomEquiv R X Y n p f) :=
  (dgHomEquiv R _ _ (p + 1)).injective <| by
    rw [dgHomEquiv_shiftHomEquiv, dgHomEquiv_dgDifferential, dgHomEquiv_dgDifferential,
      dgHomEquiv_shiftHomEquiv, map_zsmul_unit, d_castDeg R _
        (show p + 1 + (Y.shift - X.shift) = p + 1 + (Y.shift + n - (X.shift + n)) by omega)]
    simp only [add_sub_add_right_eq_sub]

/-- Shifting both objects preserves identities. -/
theorem shiftHomEquiv_dgId (X : DGShiftClosure C) (n : ℤ) :
    shiftHomEquiv R X X n 0 (dgId R X) = dgId R (⟨X.obj, X.shift + n⟩ : DGShiftClosure C) :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_shiftHomEquiv, dgHomEquiv_dgId, dgHomEquiv_dgId, castDeg_def,
      ← ModuleCat.comp_apply, XIsoOfEq_hom_comp_XIsoOfEq_hom]

/-- Shifting both objects preserves composition: the composition signs
`(-1)^((t - s) * (p + s - r))` do not change when `r`, `s` and `t` are shifted by the same
integer. -/
theorem shiftHomEquiv_dgComp {X Y Z : DGShiftClosure C} (n : ℤ) {p q m : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = m) :
    shiftHomEquiv R X Z n m (dgComp R f g h) =
      dgComp R (shiftHomEquiv R X Y n p f) (shiftHomEquiv R Y Z n q g) h :=
  (dgHomEquiv R _ _ m).injective <| by
    rw [dgHomEquiv_shiftHomEquiv, dgHomEquiv_dgComp, dgHomEquiv_dgComp, dgHomEquiv_shiftHomEquiv,
      dgHomEquiv_shiftHomEquiv, map_zsmul_unit,
      castDeg_dgComp R _ (show m + (Z.shift - X.shift) = m + (Z.shift + n - (X.shift + n)) by
        omega),
      dgComp_castDeg R _ rfl, castDeg_self]
    simp only [add_sub_add_right_eq_sub]

/-- The DG functor shifting every object of the shift closure by `n`, `X[r] ↦ X[r + n]`.  It
does not change the underlying morphisms of `C` (`MathlibExt.DGSource.DGShiftClosure.shiftHomEquiv`). -/
-- This is reducible, with the object map given explicitly, so that the image of `X[r]` is
-- reducibly `X[r + n]`.
noncomputable abbrev shiftFunctor (n : ℤ) :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (DGShiftClosure C) (DGShiftClosure C) where
  obj X := ⟨X.obj, X.shift + n⟩
  __ := EnrichedFunctor.ofDGMap (fun X ↦ (⟨X.obj, X.shift + n⟩ : DGShiftClosure C))
    (fun {X Y} p ↦ (shiftHomEquiv R X Y n p).toLinearMap)
    (fun p f ↦ shiftHomEquiv_dgDifferential R n p f) (fun X ↦ shiftHomEquiv_dgId R X n)
    (fun f g h ↦ shiftHomEquiv_dgComp R n f g h)

/-- The shift by `n` acts on morphisms by `MathlibExt.DGSource.DGShiftClosure.shiftHomEquiv`. -/
@[simp]
theorem dgMap_shiftFunctor (n : ℤ) {X Y : DGShiftClosure C} {p : ℤ} (f : DGHom R p X Y) :
    (shiftFunctor R n).dgMap p f = shiftHomEquiv R X Y n p f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- The shift is an isomorphism on Hom complexes. -/
instance isIso_shiftFunctor_map (n : ℤ) (X Y : DGShiftClosure C) :
    IsIso ((shiftFunctor R n).map X Y) :=
  have (p : ℤ) : IsIso (((shiftFunctor R n).map X Y).f p) :=
    (shiftHomEquiv R X Y n p).toModuleIso.isIso_hom
  HomologicalComplex.Hom.isIso_of_components _

/-- The comparison morphism `X[r] ⟶ X[r + n]` of degree `-n`, whose underlying morphism is
`(-1)^(n * r)` times the identity of `X`. -/
noncomputable def toShift (X : DGShiftClosure C) (n : ℤ) :
    DGHom R (-n) X ((shiftFunctor R n).obj X) :=
  (dgHomEquiv R _ _ (-n)).symm ((n * X.shift).negOnePow • castDeg R (by dsimp only; omega)
    (dgId R X.obj))

/-- The comparison morphism `X[r + n] ⟶ X[r]` of degree `n`, whose underlying morphism is
`(-1)^(n * r)` times the identity of `X`. -/
noncomputable def fromShift (X : DGShiftClosure C) (n : ℤ) :
    DGHom R n ((shiftFunctor R n).obj X) X :=
  (dgHomEquiv R _ _ n).symm ((n * X.shift).negOnePow • castDeg R (by dsimp only; omega)
    (dgId R X.obj))

/-- The underlying morphism of `X[r] ⟶ X[r + n]` is `(-1)^(n * r)` times the identity of `X`. -/
@[simp]
theorem dgHomEquiv_toShift (X : DGShiftClosure C) (n : ℤ) :
    dgHomEquiv R _ _ (-n) (toShift R X n) =
      (n * X.shift).negOnePow • castDeg R (by dsimp only; omega) (dgId R X.obj) := by
  simp [toShift]

/-- The underlying morphism of `X[r + n] ⟶ X[r]` is `(-1)^(n * r)` times the identity of `X`. -/
@[simp]
theorem dgHomEquiv_fromShift (X : DGShiftClosure C) (n : ℤ) :
    dgHomEquiv R _ _ n (fromShift R X n) =
      (n * X.shift).negOnePow • castDeg R (by dsimp only; omega) (dgId R X.obj) := by
  simp [fromShift]

/-- The comparison morphism `X[r] ⟶ X[r + n]` is closed. -/
@[simp↓]
theorem dgDifferential_toShift (X : DGShiftClosure C) (n : ℤ) :
    dgDifferential R (-n) (toShift R X n) = 0 :=
  (dgHomEquiv R _ _ (-n + 1)).injective <| by
    rw [dgHomEquiv_dgDifferential, dgHomEquiv_toShift, map_zsmul_unit, d_castDeg_dgId,
      smul_zero, smul_zero, map_zero]

/-- Two morphisms `X[r] ⟶ X[s] ⟶ X[r]` whose underlying morphisms are the same sign `u` times
the identity of `X` compose to the identity of `X[r]`: the composition sign is trivial because the
first underlying morphism has degree `0`, and `u * u = 1`. -/
private theorem dgComp_eq_dgId_of_units_smul (X : DGShiftClosure C) (s : ℤ) (u : ℤˣ) {p q : ℤ}
    {f : DGHom R p X (⟨X.obj, s⟩ : DGShiftClosure C)} {g : DGHom R q ⟨X.obj, s⟩ X}
    {hp : 0 = p + (s - X.shift)} {hq : 0 = q + (X.shift - s)}
    (hf : dgHomEquiv R _ _ p f = u • castDeg R hp (dgId R X.obj))
    (hg : dgHomEquiv R _ _ q g = u • castDeg R hq (dgId R X.obj)) (h : p + q = 0) :
    dgComp R f g h = dgId R X :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_dgComp, hf, hg, dgHomEquiv_dgId]
    simp only [← hp, mul_zero, Int.negOnePow_zero, one_smul, units_smul_dgComp, dgComp_units_smul,
      castDeg_dgId_dgComp, castDeg_castDeg, smul_smul, Int.units_mul_self]
    exact LinearMap.congr_fun (castDeg_def (C := C) R _) _

/-- The comparison morphisms `X[r] ⟶ X[r + n] ⟶ X[r]` compose to the identity of `X[r]`. -/
@[simp↓]
theorem dgComp_toShift_fromShift (X : DGShiftClosure C) (n : ℤ) :
    dgComp R (toShift R X n) (fromShift R X n) (neg_add_cancel n) = dgId R X :=
  dgComp_eq_dgId_of_units_smul R X _ _ (dgHomEquiv_toShift R X n) (dgHomEquiv_fromShift R X n) _

/-- The comparison morphisms `X[r + n] ⟶ X[r] ⟶ X[r + n]` compose to the identity of
`X[r + n]`. -/
@[simp↓]
theorem dgComp_fromShift_toShift (X : DGShiftClosure C) (n : ℤ) :
    dgComp R (fromShift R X n) (toShift R X n) (add_neg_cancel n) =
      dgId R ((shiftFunctor R n).obj X) :=
  dgComp_eq_dgId_of_units_smul R _ X.shift _ (dgHomEquiv_fromShift R X n)
    (dgHomEquiv_toShift R X n) _

/-- The comparison morphism `X[r + n] ⟶ X[r]` is closed. -/
@[simp↓]
theorem dgDifferential_fromShift (X : DGShiftClosure C) (n : ℤ) :
    dgDifferential R n (fromShift R X n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_toShift R X n) (neg_add_cancel n)
    (dgComp_toShift_fromShift R X n) (dgComp_fromShift_toShift R X n)

/-- **The comparison morphisms are natural up to the Koszul sign**: for `f : X[r] ⟶ Y[s]` of
degree `p`, `f` followed by `Y[s] ⟶ Y[s + n]` is `(-1)^(n * p)` times `X[r] ⟶ X[r + n]` followed
by the shift of `f`. -/
theorem dgComp_toShift {X Y : DGShiftClosure C} (n : ℤ) {p m : ℤ} (f : DGHom R p X Y)
    (h : p + -n = m) :
    dgComp R f (toShift R Y n) h =
      (n * p).negOnePow • dgComp R (toShift R X n) ((shiftFunctor R n).dgMap p f) (by omega) :=
  (dgHomEquiv R _ _ _).injective <| by
    rw [dgMap_shiftFunctor, map_zsmul_unit, dgHomEquiv_dgComp, dgHomEquiv_dgComp,
      dgHomEquiv_toShift, dgHomEquiv_toShift, dgHomEquiv_shiftHomEquiv, dgComp_units_smul,
      dgComp_castDeg_dgId, units_smul_dgComp, castDeg_dgId_dgComp, castDeg_castDeg, smul_smul,
      smul_smul, smul_smul]
    congr 1
    simp only [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨n * (Y.shift - X.shift), by ring⟩

/-- **The inverse comparison morphisms are natural up to the Koszul sign**: for
`f : X[r] ⟶ Y[s]` of degree `p`, the shift of `f` followed by `Y[s + n] ⟶ Y[s]` is
`(-1)^(n * p)` times `X[r + n] ⟶ X[r]` followed by `f`. -/
theorem dgComp_fromShift {X Y : DGShiftClosure C} (n : ℤ) {p m : ℤ} (f : DGHom R p X Y)
    (h : p + n = m) :
    dgComp R ((shiftFunctor R n).dgMap p f) (fromShift R Y n) h =
      (n * p).negOnePow • dgComp R (fromShift R X n) f (by omega) :=
  (dgHomEquiv R _ _ _).injective <| by
    rw [dgMap_shiftFunctor, map_zsmul_unit, dgHomEquiv_dgComp, dgHomEquiv_dgComp,
      dgHomEquiv_fromShift, dgHomEquiv_fromShift, dgHomEquiv_shiftHomEquiv, dgComp_units_smul,
      dgComp_castDeg_dgId, units_smul_dgComp, castDeg_dgId_dgComp, castDeg_castDeg, smul_smul,
      smul_smul, smul_smul]
    congr 1
    simp only [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨-(n * p), by ring⟩

end DGShiftClosure

end MathlibExt.DGSource

namespace CategoryTheory.EnrichedFunctor

open MathlibExt.DGSource DGShiftClosure

universe v u u₂

/-! ### Functoriality -/

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u₂} [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- The action of a DG functor on morphisms `X[r] ⟶ Y[s]` of degree `n`: its action on the
underlying morphisms `X ⟶ Y` of degree `n + (s - r)`. -/
noncomputable def mapDGShiftClosureHom (X Y : DGShiftClosure C) (n : ℤ) :
    DGHom R n X Y →ₗ[R]
      DGHom R n (⟨F.obj X.obj, X.shift⟩ : DGShiftClosure D) ⟨F.obj Y.obj, Y.shift⟩ :=
  (dgHomEquiv R _ _ n).symm.toLinearMap ∘ₗ F.dgMap (n + (Y.shift - X.shift)) ∘ₗ
    (dgHomEquiv R X Y n).toLinearMap

/-- The underlying morphism of the image of a morphism of the shift closure is the image of its
underlying morphism. -/
@[simp]
theorem dgHomEquiv_mapDGShiftClosureHom {X Y : DGShiftClosure C} {n : ℤ} (f : DGHom R n X Y) :
    dgHomEquiv R _ _ n (F.mapDGShiftClosureHom X Y n f) =
      F.dgMap (n + (Y.shift - X.shift)) (dgHomEquiv R X Y n f) := by
  simp [mapDGShiftClosureHom]

/-- The DG functor between shift closures induced by a DG functor `F`, sending `X[r]` to
`(F X)[r]` and applying `F` to the underlying morphisms. -/
-- This is reducible, with the object map given explicitly, so that the image of `X[r]` is
-- reducibly `(F X)[r]`.
noncomputable abbrev mapDGShiftClosure :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (DGShiftClosure C) (DGShiftClosure D) where
  obj X := ⟨F.obj X.obj, X.shift⟩
  __ := EnrichedFunctor.ofDGMap (fun X ↦ (⟨F.obj X.obj, X.shift⟩ : DGShiftClosure D))
    (fun {X Y} n ↦ F.mapDGShiftClosureHom X Y n)
    (fun {X Y} n f ↦ (dgHomEquiv R _ _ (n + 1)).injective <| by
      rw [dgHomEquiv_mapDGShiftClosureHom, dgHomEquiv_dgDifferential, dgHomEquiv_dgDifferential,
        dgHomEquiv_mapDGShiftClosureHom, map_zsmul_unit, dgMap_d])
    (fun X ↦ (dgHomEquiv R _ _ 0).injective <| by
      rw [dgHomEquiv_mapDGShiftClosureHom, dgHomEquiv_dgId, dgHomEquiv_dgId]
      simp only [← castDeg_def, dgMap_castDeg, dgMap_dgId])
    (fun {X Y Z p q n} f g h ↦ (dgHomEquiv R _ _ n).injective <| by
      rw [dgHomEquiv_mapDGShiftClosureHom, dgHomEquiv_dgComp, dgHomEquiv_dgComp, map_zsmul_unit,
        dgMap_dgComp, dgHomEquiv_mapDGShiftClosureHom, dgHomEquiv_mapDGShiftClosureHom])

/-- The induced DG functor acts on morphisms by
`CategoryTheory.EnrichedFunctor.mapDGShiftClosureHom`. -/
@[simp]
theorem dgMap_mapDGShiftClosure {X Y : DGShiftClosure C} {n : ℤ} (f : DGHom R n X Y) :
    F.mapDGShiftClosure.dgMap n f = F.mapDGShiftClosureHom X Y n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- The induced DG functor commutes with shifting every object: the images of a morphism under the
two composites have the same underlying morphism of `D`. -/
theorem mapDGShiftClosureHom_shiftHomEquiv {X Y : DGShiftClosure C} (n : ℤ) {p : ℤ}
    (f : DGHom R p X Y) :
    F.mapDGShiftClosureHom _ _ p (shiftHomEquiv R X Y n p f) =
      shiftHomEquiv R _ _ n p (F.mapDGShiftClosureHom X Y p f) :=
  (dgHomEquiv R _ _ p).injective <| by
    -- After the first rewrite the right side's objects are unreduced projections such as
    -- `{ obj := X.obj, shift := X.shift + n }.shift`, which keyed matching does not unify with the
    -- pattern of `dgHomEquiv_shiftHomEquiv`: its second use is given the objects explicitly.
    rw [dgHomEquiv_mapDGShiftClosureHom, dgHomEquiv_shiftHomEquiv,
      dgHomEquiv_shiftHomEquiv R (X := ⟨F.obj X.obj, X.shift⟩) (Y := ⟨F.obj Y.obj, Y.shift⟩),
      dgHomEquiv_mapDGShiftClosureHom, dgMap_castDeg]

/-- The induced DG functor sends the comparison morphism `X[r] ⟶ X[r + n]` to the comparison
morphism `(F X)[r] ⟶ (F X)[r + n]`. -/
@[simp]
theorem mapDGShiftClosureHom_toShift (X : DGShiftClosure C) (n : ℤ) :
    F.mapDGShiftClosureHom _ _ (-n) (toShift R X n) = toShift R ⟨F.obj X.obj, X.shift⟩ n :=
  (dgHomEquiv R _ _ (-n)).injective <| by
    rw [dgHomEquiv_mapDGShiftClosureHom, dgHomEquiv_toShift,
      dgHomEquiv_toShift R ⟨F.obj X.obj, X.shift⟩ n, map_zsmul_unit, dgMap_castDeg, dgMap_dgId]

/-- The induced DG functor sends the comparison morphism `X[r + n] ⟶ X[r]` to the comparison
morphism `(F X)[r + n] ⟶ (F X)[r]`. -/
@[simp]
theorem mapDGShiftClosureHom_fromShift (X : DGShiftClosure C) (n : ℤ) :
    F.mapDGShiftClosureHom _ _ n (fromShift R X n) = fromShift R ⟨F.obj X.obj, X.shift⟩ n :=
  (dgHomEquiv R _ _ n).injective <| by
    rw [dgHomEquiv_mapDGShiftClosureHom, dgHomEquiv_fromShift,
      dgHomEquiv_fromShift R ⟨F.obj X.obj, X.shift⟩ n, map_zsmul_unit, dgMap_castDeg, dgMap_dgId]

end CategoryTheory.EnrichedFunctor
