/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Representable.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGCochainCategory
public import MathlibExt.CategoryTheory.DGSource.DGNaturalTransformation
public import MathlibExt.CategoryTheory.DGSource.DGOpposite

/-!
# Representable DG modules and the Yoneda lemma

A right DG module over a DG category `C` is a DG functor `Cᵒᵖ ⥤ C(R)` into the DG category of
cochain complexes of `R`-modules.  Every object `X` of `C` gives the **representable** right
module `Hom(-, X)`: it sends `Y` to the Hom complex `Hom(Y, X)`, and a morphism `f : Z ⟶ Y` of
degree `n` acts by precomposition, the degree-`n` cochain `g ↦ f ≫ g` from `Hom(Y, X)` to
`Hom(Z, X)`.  No sign enters: the Leibniz rule makes precomposition commute with the
differentials, and the Koszul sign of composition in the opposite DG category is exactly the one
of composition of cochains.

A morphism `u : X ⟶ X'` of degree `n` acts on the values `Hom(Y, X)` by **postcomposition** in
Keller's order, `g ↦ u ∘ g = (-1) ^ (p * n) • (g ≫ u)` for `g` of degree `p`.  With this sign
postcomposition commutes with the differentials, identities and composition on the nose, and it
commutes with precomposition up to the Koszul sign `(-1) ^ (p * n)`; this is what makes it a
morphism of right DG modules in `MathlibExt.CategoryTheory.DGSource.DGYoneda`.

The **Yoneda lemma** identifies DG natural transformations `Hom(-, X) ⟶ F`, that is closed
degree-zero morphisms of right DG modules, with the closed degree-zero elements of `F(X)`: a
transformation `η` goes to `η_X(1_X)`, and a closed element `x` of degree zero goes to the
transformation whose component at `Y` sends `g : Y ⟶ X` of degree `p` to `F(g)(x)`.  For a
representable target `Hom(-, X')` the closed degree-zero elements are the closed degree-zero
morphisms `X ⟶ X'`, and the transformation they give is postcomposition.

## Main definitions

* `MathlibExt.DGSource.dgRepresentable`: the representable right DG module `Hom(-, X)`.
* `MathlibExt.DGSource.dgPostcomp`: postcomposition with a homogeneous morphism, as a morphism of the DG
  category of cochain complexes between values of representable modules.
* `MathlibExt.DGSource.dgYonedaEquiv`: the Yoneda bijection between DG natural transformations out of
  `Hom(-, X)` and closed degree-zero elements of `F(X)`.
* `MathlibExt.DGSource.dgRepresentableNatTransEquiv`: DG natural transformations between representables
  are the closed degree-zero morphisms between the representing objects.

## Main results

* `MathlibExt.DGSource.dgRepresentable_dgMap_v`: a morphism acts on the representable module by
  precomposition.
* `MathlibExt.DGSource.dgPostcomp_dgDifferential`, `MathlibExt.DGSource.dgPostcomp_dgId` and
  `MathlibExt.DGSource.dgPostcomp_dgComp`: postcomposition commutes with the differentials, identities and
  composition.
* `MathlibExt.DGSource.dgComp_dgMap_dgPostcomp`: postcomposition commutes with precomposition up to the
  Koszul sign.
* `MathlibExt.DGSource.dgMap_dgComp_v_apply`: a right DG module carries a composite to the composite of
  cochains in the reversed order.
* `MathlibExt.DGSource.dgYonedaEquiv_apply_coe` and `MathlibExt.DGSource.dgApp_dgYonedaEquiv_symm_v`: the two directions
  of the Yoneda bijection.
* `MathlibExt.DGSource.dgApp_dgRepresentableNatTransEquiv_symm_v`: the transformation between representables
  given by a closed morphism is postcomposition with it.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* G. M. Kelly, *Basic concepts of enriched category theory*, Section 1.9, for the Yoneda lemma
  on underlying sets of natural transformations.
-/

public section

open CategoryTheory Opposite CochainComplex.HomComplex

namespace MathlibExt.DGSource

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-! ### The representable right DG module -/

/-- **Precomposition** with a morphism `f : Z ⟶ Y` of degree `n`, as a degree-`n` cochain from
`Hom(Y, X)` to `Hom(Z, X)`, linear in `f`.  Its component on morphisms of degree `p` sends `g` to
`f ≫ g` (`MathlibExt.DGSource.dgPrecomp_v`). -/
noncomputable def dgPrecomp (X : C) {Y Z : C} (n : ℤ) :
    DGHom R n Z Y →ₗ[R] Cochain (dgHomComplex R Y X) (dgHomComplex R Z X) n where
  toFun f := Cochain.mk fun p q hpq ↦ ModuleCat.ofHom <|
    LinearMap.mk₂ R (fun (f : DGHom R n Z Y) (g : DGHom R p Y X) ↦ dgComp R f g (by omega))
      (fun _ _ _ ↦ add_dgComp R _ _ _ _) (fun _ _ _ ↦ smul_dgComp R _ _ _ _)
      (fun _ _ _ ↦ dgComp_add R _ _ _ _) (fun _ _ _ ↦ dgComp_smul R _ _ _ _) f
  map_add' f f' := by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    ext g
    simp only [Cochain.mk_v, ModuleCat.hom_ofHom, Cochain.add_v, ModuleCat.hom_add,
      LinearMap.add_apply, LinearMap.mk₂_apply, add_dgComp]
  map_smul' r f := by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    ext g
    simp only [Cochain.mk_v, ModuleCat.hom_ofHom, Cochain.smul_v, ModuleCat.hom_smul,
      LinearMap.smul_apply, LinearMap.mk₂_apply, smul_dgComp, RingHom.id_apply]

/-- The component of precomposition with `f` on a morphism `g` is the composite `f ≫ g`. -/
@[simp]
theorem dgPrecomp_v (X : C) {Y Z : C} {n : ℤ} (f : DGHom R n Z Y) (p q : ℤ)
    (hpq : p + n = q) (g : DGHom R p Y X) :
    ((dgPrecomp R X n f).v p q hpq).hom g = dgComp R f g (by omega) :=
  (rfl)

/-- Precomposition commutes with the differentials: by the Leibniz rule, precomposing with `d f`
is the differential of precomposing with `f` in the Hom complex of cochains. -/
@[simp]
theorem dgPrecomp_dgDifferential (X : C) {Y Z : C} {n : ℤ} (f : DGHom R n Z Y) :
    dgPrecomp R X (n + 1) (dgDifferential R n f) = δ n (n + 1) (dgPrecomp R X n f) := by
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  ext g
  rw [δ_v n (n + 1) rfl _ p q hpq (p + n) (p + 1) (by omega) rfl]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, dgPrecomp_v]
  rw [dgHomComplex_d_dgComp R rfl rfl (by omega), Int.negOnePow_succ, Units.val_neg, neg_smul,
    Units.smul_def, add_neg_cancel_right]

/-- Precomposition with an identity is the identity cochain. -/
@[simp]
theorem dgPrecomp_dgId (X Y : C) :
    dgPrecomp R X 0 (dgId R Y) = Cochain.ofHom (𝟙 (dgHomComplex R Y X)) := by
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  obtain rfl : q = p := by omega
  ext g
  rw [Cochain.ofHom_v, dgPrecomp_v, dgId_dgComp, HomologicalComplex.id_f, ModuleCat.id_apply]

/-- Precomposition is contravariantly functorial: precomposing with `g ≫ f` is precomposing with
`f` and then with `g`, with no sign. -/
@[simp]
theorem dgPrecomp_dgComp (X : C) {Y Z W : C} {p q n : ℤ} (f : DGHom R p Z Y)
    (g : DGHom R q W Z) (h : q + p = n) :
    dgPrecomp R X n (dgComp R g f h) =
      (dgPrecomp R X p f).comp (dgPrecomp R X q g) (by omega) := by
  refine Cochain.ext _ _ fun r s hrs ↦ ?_
  ext x
  rw [Cochain.comp_v (dgPrecomp R X p f) (dgPrecomp R X q g) (by omega : p + q = n) r (r + p) s
    (by omega) (by omega)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, dgPrecomp_v]
  exact dgComp_assoc R g f x h (add_comm p r) (by omega)

/-- Precomposition intertwines composition in the opposite DG category with composition of
cochains: the Koszul signs of the two compositions agree. -/
private theorem dgPrecomp_dgComp_op (X : C) {Y Z W : C} {p q n : ℤ} (f : DGHom R p Z Y)
    (g : DGHom R q W Z) (h : p + q = n) :
    dgPrecomp R X n (dgComp (C := Cᵒᵖ) R (X := op Y) (Y := op Z) (Z := op W) f g h) =
      dgComp R (C := CochainComplex (ModuleCat.{v} R) ℤ) (dgPrecomp R X p f)
        (dgPrecomp R X q g) h := by
  rw [dgComp_op, map_zsmul_unit, dgPrecomp_dgComp]
  exact (dgComp_linearHomComplex R _ _ h).symm

/-- The **representable right DG module** `Hom(-, X)` of an object `X` of a DG category: the DG
functor from the opposite DG category to cochain complexes sending `Y` to the Hom complex
`Hom(Y, X)`, on which a morphism `f : Z ⟶ Y` of degree `n` acts by precomposition. -/
-- The body is exposed so that `(dgRepresentable R X).obj Y` is definitionally `Hom(Y, X)`, as
-- for `CategoryTheory.EnrichedFunctor.ofDGMap`.
@[expose]
noncomputable def dgRepresentable (X : C) :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) Cᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℤ) :=
  EnrichedFunctor.ofDGMap (fun Y ↦ dgHomComplex R Y.unop X)
    (fun {Y Z} n ↦ dgPrecomp R X (Y := Y.unop) (Z := Z.unop) n)
    (fun {Y Z} n f ↦ by
      rw [dgDifferential_linearHomComplex]
      -- The differential of the opposite DG category is the original one (`dgDifferential_op`).
      exact dgPrecomp_dgDifferential R X f)
    (fun Y ↦ by
      rw [dgId_linearHomComplex]
      cases Y
      exact (congrArg (dgPrecomp R X 0) (dgId_op R _)).trans (dgPrecomp_dgId R X _))
    (fun {Y Z W p q n} f g h ↦ by
      cases Y
      cases Z
      cases W
      exact dgPrecomp_dgComp_op R X f g h)

/-- The representable module `Hom(-, X)` sends `Y` to the Hom complex `Hom(Y, X)`. -/
theorem dgRepresentable_obj (X : C) (Y : Cᵒᵖ) :
    (dgRepresentable R X).obj Y = dgHomComplex R Y.unop X :=
  rfl

/-- **A morphism acts on the representable module by precomposition** with it. -/
@[simp]
theorem dgRepresentable_dgMap (X : C) {Y Z : C} {n : ℤ} (f : DGHom R n Z Y) :
    (dgRepresentable R X).dgMap n (X := op Y) (Y := op Z) f = dgPrecomp R X n f :=
  EnrichedFunctor.dgMap_ofDGMap (C := Cᵒᵖ) (fun Y ↦ dgHomComplex R Y.unop X)
    (fun {Y Z} n ↦ dgPrecomp R X (Y := Y.unop) (Z := Z.unop) n) _ _ _ n f

/-! ### Postcomposition -/

/-- **Postcomposition** with a morphism `u : X ⟶ X'` of degree `n`, as a degree-`n` morphism
`Hom(Y, X) ⟶ Hom(Y, X')` of the DG category of cochain complexes between the values at `Y` of the
representable modules of `X` and `X'`, linear in `u`.  It is precomposition with `u` in the
opposite DG category, so its component on morphisms of degree `p` sends `g` to the Keller-ordered
composite `u ∘ g = (-1) ^ (p * n) • (g ≫ u)` (`MathlibExt.DGSource.dgPostcomp_v`). -/
noncomputable def dgPostcomp (Y : Cᵒᵖ) {X X' : C} (n : ℤ) :
    DGHom R n X X' →ₗ[R] DGHom R n ((dgRepresentable R X).obj Y) ((dgRepresentable R X').obj Y) :=
  dgPrecomp (C := Cᵒᵖ) R Y (Y := op X) (Z := op X') n

/-- The component of postcomposition with `u` on a morphism `g` of degree `p` is the
Keller-ordered composite `(-1) ^ (p * n) • (g ≫ u)`. -/
@[simp]
theorem dgPostcomp_v (Y : C) {X X' : C} {n : ℤ} (u : DGHom R n X X') (p q : ℤ)
    (hpq : p + n = q) (g : DGHom R p Y X) :
    ((dgPostcomp R (op Y) n u : Cochain ((dgRepresentable R X).obj (op Y))
      ((dgRepresentable R X').obj (op Y)) n).v p q hpq).hom g =
      (p * n).negOnePow • dgComp R g u hpq :=
  (dgPrecomp_v (C := Cᵒᵖ) R (op Y) (Y := op X) (Z := op X') u p q hpq g).trans <| by
    rw [dgComp_op, mul_comm]

/-- **Postcomposition commutes with the differentials**: postcomposing with `d u` is the
differential of postcomposing with `u`, by the Leibniz rule in Keller's order. -/
@[simp]
theorem dgPostcomp_dgDifferential (Y : Cᵒᵖ) {X X' : C} {n : ℤ} (u : DGHom R n X X') :
    dgPostcomp R Y (n + 1) (dgDifferential R n u) = dgDifferential R n (dgPostcomp R Y n u) :=
  (dgPrecomp_dgDifferential (C := Cᵒᵖ) R Y (Y := op X) (Z := op X') u).trans
    (dgDifferential_linearHomComplex R (F := (dgRepresentable R X).obj Y)
      (G := (dgRepresentable R X').obj Y) n (dgPostcomp R Y n u)).symm

/-- Postcomposition with an identity is the identity. -/
@[simp]
theorem dgPostcomp_dgId (Y : Cᵒᵖ) (X : C) :
    dgPostcomp R Y 0 (dgId R X) = dgId R ((dgRepresentable R X).obj Y) :=
  ((congrArg (dgPrecomp (C := Cᵒᵖ) R Y 0) (dgId_op R X).symm).trans
    (dgPrecomp_dgId (C := Cᵒᵖ) R Y (op X))).trans (dgId_linearHomComplex R _).symm

/-- **Postcomposition is functorial**: postcomposing with `u ≫ v` is postcomposing with `u` and
then with `v`. -/
@[simp]
theorem dgPostcomp_dgComp (Y : Cᵒᵖ) {X X' X'' : C} {p q n : ℤ} (u : DGHom R p X X')
    (v : DGHom R q X' X'') (h : p + q = n) :
    dgPostcomp R Y n (dgComp R u v h) = dgComp R (dgPostcomp R Y p u) (dgPostcomp R Y q v) h := by
  -- In the opposite category `u ≫ v` is `v` followed by `u`, up to the Koszul sign which is also
  -- the sign of composition of cochains.
  have e := dgPrecomp_dgComp (C := Cᵒᵖ) R Y (Y := op X) (Z := op X') (W := op X'') u v
    (by omega : q + p = n)
  rw [dgComp_op, map_zsmul_unit] at e
  calc dgPostcomp R Y n (dgComp R u v h)
      = (q * p).negOnePow • ((q * p).negOnePow • dgPostcomp R Y n (dgComp R u v h)) := by
        rw [smul_smul, Int.units_mul_self, one_smul]
    _ = _ := by
        rw [dgComp_linearHomComplex, mul_comm p q]
        exact congrArg ((q * p).negOnePow • ·) e

/-- Postcomposition with `u`, that is precomposition with `u` in the opposite DG category,
commutes with precomposition with `f` up to the Koszul sign of the degrees. -/
private theorem dgPrecomp_comp_dgPrecomp_op {X X' Y Z : C} {p n m : ℤ} (f : DGHom R p Z Y)
    (u : DGHom R n X X') (h : p + n = m) (h' : n + p = m) :
    (dgPrecomp R X p f).comp (dgPrecomp (C := Cᵒᵖ) R (op Z) (Y := op X) (Z := op X') n u) h =
      (p * n).negOnePow • (dgPrecomp (C := Cᵒᵖ) R (op Y) (Y := op X) (Z := op X') n u).comp
        (dgPrecomp R X' p f) h' := by
  refine Cochain.ext _ _ fun r s hrs ↦ ?_
  ext g
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ h r (r + p) s rfl (by omega),
    Cochain.comp_v _ _ h' r (r + n) s rfl (by omega)]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
    dgPrecomp_v, dgComp_op, dgComp_units_smul, smul_smul]
  rw [dgComp_assoc R f g u (by omega : p + r = r + p) rfl (by omega)]
  congr 1
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨0, by ring⟩

/-- **Postcomposition commutes with the module action** up to the Koszul sign `(-1) ^ (p * n)` of
the degrees: acting on `Hom(-, X)` by `f : Y ⟶ Z` of degree `p` in `Cᵒᵖ` and then postcomposing
with `u : X ⟶ X'` of degree `n` is `(-1) ^ (p * n)` times postcomposing first and acting by `f`
on `Hom(-, X')` afterwards. -/
theorem dgComp_dgMap_dgPostcomp {X X' : C} {Y Z : Cᵒᵖ} {p n m : ℤ} (f : DGHom R p Y Z)
    (u : DGHom R n X X') (h : p + n = m) (h' : n + p = m) :
    dgComp R ((dgRepresentable R X).dgMap p f) (dgPostcomp R Z n u) h =
      (p * n).negOnePow • dgComp R (dgPostcomp R Y n u) ((dgRepresentable R X').dgMap p f) h' := by
  rw [dgComp_linearHomComplex, dgComp_linearHomComplex]
  induction Y with | op Y => ?_
  induction Z with | op Z => ?_
  simp only [dgRepresentable_dgMap]
  -- The remaining `rfl` unfolds `dgPostcomp` to precomposition in the opposite DG category.
  exact congrArg ((p * n).negOnePow • ·)
    ((dgPrecomp_comp_dgPrecomp_op R (C := C) (Y := Y) (Z := Z) f u h h').trans
      (by rw [mul_comm p n]; rfl))

/-! ### The Yoneda lemma -/

section Yoneda

variable {R} (X : C)
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) Cᵒᵖ
    (CochainComplex (ModuleCat.{v} R) ℤ))

/-- For a closed element `x` of degree zero, `g ↦ F(g)(x)` commutes with the differentials. -/
private theorem dgMap_dgDifferential_v_apply {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) {Y : Cᵒᵖ} {p : ℤ} (g : DGHom R p (op X) Y) :
    ((F.dgMap (p + 1) (dgDifferential R p g) :
        Cochain (F.obj (op X)) (F.obj Y) (p + 1)).v 0 (p + 1) (zero_add _)).hom x =
      ((F.obj Y).d p (p + 1)).hom
        (((F.dgMap p g : Cochain (F.obj (op X)) (F.obj Y) p).v 0 p (zero_add p)).hom x) := by
  have key := δ_v p (p + 1) rfl (F.dgMap p g) 0 (p + 1) (zero_add _) p 1 (by omega) rfl
  rw [F.dgMap_dgDifferential, dgDifferential_linearHomComplex, key]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, hx, map_zero, smul_zero,
    add_zero]

/-- A DG functor out of the opposite category carries a composite `f ≫ g` to the composite of
cochains in the reversed order: evaluated on an element `x` of degree `n`, it is `F(f)(F(g)(x))`. -/
theorem dgMap_dgComp_v_apply {Y Z : C} {q r s : ℤ} (f : DGHom R q Z Y)
    (g : DGHom R r Y X) (h : q + r = s) {n : ℤ} (x : (F.obj (op X)).X n) (k t : ℤ)
    (hk : n + r = k) (ht : n + s = t) :
    ((F.dgMap s (X := op X) (Y := op Z) (dgComp R f g h : DGHom R s Z X) :
        Cochain (F.obj (op X)) (F.obj (op Z)) s).v n t ht).hom x =
      ((F.dgMap q (X := op Y) (Y := op Z) f :
        Cochain (F.obj (op Y)) (F.obj (op Z)) q).v k t (by omega)).hom
          (((F.dgMap r (X := op X) (Y := op Y) g :
            Cochain (F.obj (op X)) (F.obj (op Y)) r).v n k hk).hom x) := by
  -- In the opposite category the composite is `g` followed by `f`, up to a Koszul sign which
  -- cancels against the sign of composition of cochains.
  have e : dgComp R f g h =
      (r * q).negOnePow • dgComp (C := Cᵒᵖ) R (X := op X) (Y := op Y) (Z := op Z) g f
        (by omega) := by
    rw [dgComp_op, smul_smul, Int.units_mul_self, one_smul]
  have e' : (F.dgMap s (X := op X) (Y := op Z) (dgComp R f g h : DGHom R s Z X) :
      Cochain (F.obj (op X)) (F.obj (op Z)) s) =
        Cochain.comp (F.dgMap r (X := op X) (Y := op Y) g) (F.dgMap q (X := op Y) (Y := op Z) f)
          (by omega) := by
    rw [e, map_zsmul_unit, F.dgMap_dgComp, dgComp_linearHomComplex]
    -- The two signs act through the same scalar action, by the identification of the Hom
    -- complexes of cochain complexes with cochains.
    exact (smul_smul _ _ _).trans ((congrArg (· • _) (Int.units_mul_self _)).trans (one_smul _ _))
  have key := Cochain.comp_v (F.dgMap r (X := op X) (Y := op Y) g)
    (F.dgMap q (X := op Y) (Y := op Z) f) (by omega : r + q = s) n k t hk (by omega)
  rw [e', key, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The component at `Y` of the transformation given by a closed element `x` of degree zero: the
chain map `Hom(Y, X) ⟶ F(Y)` sending `g` to `F(g)(x)`. -/
private noncomputable def yonedaHom {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) (Y : Cᵒᵖ) :
    (dgRepresentable R X).obj Y ⟶ F.obj Y where
  f p := ModuleCat.ofHom (cochainEval R x p p (zero_add p) ∘ₗ F.dgMap p (X := op X) (Y := Y))
  comm' p q hpq := by
    obtain rfl : q = p + 1 := hpq.symm
    ext g
    exact (congrArg ((F.obj Y).d p (p + 1)).hom (cochainEval_apply R x p p (zero_add p) _)).trans
      ((dgMap_dgDifferential_v_apply X F hx g).symm.trans
        (cochainEval_apply R x (p + 1) (p + 1) (zero_add _) _).symm)

private theorem yonedaHom_f_apply {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) (Y : Cᵒᵖ) (p : ℤ) (g : DGHom R p (op X) Y) :
    ((yonedaHom X F hx Y).f p).hom g =
      ((F.dgMap p g : Cochain (F.obj (op X)) (F.obj Y) p).v 0 p (zero_add p)).hom x :=
  cochainEval_apply R x p p (zero_add p) (F.dgMap p g)

/-- The component at `Y` of the transformation given by a closed element of degree zero, as a
closed degree-zero morphism of the DG category of cochain complexes. -/
private noncomputable def yonedaApp {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) (Y : Cᵒᵖ) :
    DGHom R 0 ((dgRepresentable R X).obj Y) (F.obj Y) :=
  Cochain.ofHom (yonedaHom X F hx Y)

private theorem yonedaApp_v {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) (Y : Cᵒᵖ) (p : ℤ) :
    (yonedaApp X F hx Y : Cochain ((dgRepresentable R X).obj Y) (F.obj Y) 0).v p p (add_zero p) =
      (yonedaHom X F hx Y).f p :=
  Cochain.ofHom_v _ p

/-- The components given by a closed element of degree zero are natural. -/
private theorem yonedaApp_naturality {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) {Y Z : Cᵒᵖ} (n : ℤ) (f : DGHom R n Y Z) :
    dgComp R ((dgRepresentable R X).dgMap n f) (yonedaApp X F hx Z) (add_zero n) =
      dgComp R (yonedaApp X F hx Y) (F.dgMap n f) (zero_add n) := by
  cases Y
  cases Z
  refine Cochain.ext _ _ fun r s hrs ↦ ?_
  have k₁ := dgComp_v R ((dgRepresentable R X).dgMap n f)
    (yonedaApp X F hx _) (add_zero n) r s s hrs (add_zero s)
  have k₂ := dgComp_v R (yonedaApp X F hx _) (F.dgMap n f) (zero_add n) r r s
    (add_zero r) hrs
  rw [k₁, k₂]
  ext g
  simp only [mul_zero, zero_mul, Int.negOnePow_zero, one_smul, yonedaApp_v,
    ModuleCat.hom_comp, LinearMap.comp_apply, dgRepresentable_dgMap]
  -- Unfolding the two components, both sides are `F(f)(F(g)(x))`.
  exact (yonedaHom_f_apply X F hx _ s _).trans
    ((dgMap_dgComp_v_apply X F f g _ x r s (zero_add r) (zero_add s)).trans
      (congrArg _ (yonedaHom_f_apply X F hx _ r g).symm))

/-- The DG natural transformation `Hom(-, X) ⟶ F` given by a closed element of degree zero. -/
private noncomputable def yonedaNatTrans {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) : DGNatTrans (dgRepresentable R X) F :=
  DGNatTrans.ofDGApp (yonedaApp X F hx)
    (fun _ ↦ (mem_dgCycles R).2 ((dgDifferential_linearHomComplex R 0 _).trans (δ_ofHom _)))
    (yonedaApp_naturality X F hx)

private theorem dgApp_dgYonedaNatTrans {x : (F.obj (op X)).X 0}
    (hx : ((F.obj (op X)).d 0 1).hom x = 0) (Y : Cᵒᵖ) :
    (yonedaNatTrans X F hx).dgApp Y = yonedaApp X F hx Y :=
  DGNatTrans.dgApp_ofDGApp _ _ (yonedaApp_naturality X F hx) Y

/-- The value at the identity of the component at `X` of a DG natural transformation out of
`Hom(-, X)` is closed. -/
private theorem dgApp_v_dgId_mem_ker (α : DGNatTrans (dgRepresentable R X) F) :
    ((α.dgApp (op X) : Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op X)) 0).v 0 0
        (add_zero 0)).hom (dgId R X) ∈ LinearMap.ker ((F.obj (op X)).d 0 1).hom :=
  Cochain.v_apply_mem_ker_of_δ_eq_zero _
    ((dgDifferential_linearHomComplex R 0 _).symm.trans
      ((mem_dgCycles R).1 (α.dgApp_mem_dgCycles _)))
    (dgDifferential_dgId R X)

/-- **A DG natural transformation out of `Hom(-, X)` is determined by its value at the
identity**: its component at `Y` sends `g` to `F(g)` applied to that value. -/
private theorem dgApp_v_apply (α : DGNatTrans (dgRepresentable R X) F) {Y : C} {p : ℤ}
    (g : DGHom R p Y X) :
    ((α.dgApp (op Y) : Cochain ((dgRepresentable R X).obj (op Y)) (F.obj (op Y)) 0).v p p
        (add_zero p)).hom g =
      ((F.dgMap p (X := op X) (Y := op Y) g : Cochain (F.obj (op X)) (F.obj (op Y)) p).v 0 p
          (zero_add p)).hom
        (((α.dgApp (op X) : Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op X)) 0).v 0 0
          (add_zero 0)).hom (dgId R X)) := by
  have k₁ := dgComp_v R ((dgRepresentable R X).dgMap p (X := op X) (Y := op Y) g)
    (α.dgApp (op Y)) (add_zero p) 0 p p (zero_add p) (add_zero p)
  have k₂ := dgComp_v R (α.dgApp (op X)) (F.dgMap p (X := op X) (Y := op Y) g) (zero_add p) 0 0
    p (add_zero 0) (zero_add p)
  have key := congrArg (fun z : Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op Y)) p ↦
    ModuleCat.Hom.hom (z.v 0 p (zero_add p)) (dgId R X))
    (α.dgComp_dgMap_dgApp (X := op X) (Y := op Y) g)
  rw [k₁, k₂] at key
  simp only [mul_zero, zero_mul, Int.negOnePow_zero, one_smul, ModuleCat.hom_comp,
    dgRepresentable_dgMap] at key
  -- The left side of `key` is the component at `Y` evaluated on `g ≫ 1_X = g`.
  exact (congrArg (ModuleCat.Hom.hom ((α.dgApp (op Y) :
    Cochain ((dgRepresentable R X).obj (op Y)) (F.obj (op Y)) 0).v p p (add_zero p)))
      (dgComp_dgId R g)).symm.trans key

/-- **The Yoneda lemma for right DG modules**: DG natural transformations `Hom(-, X) ⟶ F` are the
closed degree-zero elements of `F(X)`.  A transformation goes to the image of the identity of `X`
under its component at `X` (`MathlibExt.DGSource.dgYonedaEquiv_apply_coe`), and a closed element `x` goes to
the transformation sending `g : Y ⟶ X` to `F(g)(x)` (`MathlibExt.DGSource.dgApp_dgYonedaEquiv_symm_v`). -/
noncomputable def dgYonedaEquiv :
    DGNatTrans (dgRepresentable R X) F ≃ LinearMap.ker ((F.obj (op X)).d 0 1).hom where
  toFun α := ⟨_, dgApp_v_dgId_mem_ker X F α⟩
  invFun x := yonedaNatTrans X F (LinearMap.mem_ker.1 x.2)
  left_inv α := by
    refine DGNatTrans.ext_dgApp fun Y ↦ ?_
    cases Y with | op Y => ?_
    refine Cochain.ext₀ _ _ fun p ↦ ?_
    ext g
    dsimp only
    rw [dgApp_dgYonedaNatTrans, yonedaApp_v]
    exact (yonedaHom_f_apply X F _ (op Y) p g).trans (dgApp_v_apply X F α g).symm
  right_inv x := by
    refine Subtype.ext ?_
    have hF : (F.dgMap 0 (X := op X) (Y := op X) (dgId R X) :
        Cochain (F.obj (op X)) (F.obj (op X)) 0) = Cochain.ofHom (𝟙 _) := by
      rw [← dgId_op, F.dgMap_dgId, dgId_linearHomComplex]
    dsimp only
    rw [dgApp_dgYonedaNatTrans, yonedaApp_v, yonedaHom_f_apply, hF, Cochain.ofHom_v,
      HomologicalComplex.id_f, ModuleCat.id_apply]

/-- The Yoneda bijection sends a transformation to the image of the identity of `X` under its
component at `X`. -/
@[simp]
theorem dgYonedaEquiv_apply_coe (α : DGNatTrans (dgRepresentable R X) F) :
    (dgYonedaEquiv X F α : (F.obj (op X)).X 0) =
      ((α.dgApp (op X) : Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op X)) 0).v 0 0
        (add_zero 0)).hom (dgId R X) :=
  (rfl)

private theorem dgYonedaEquiv_symm_apply (x : LinearMap.ker ((F.obj (op X)).d 0 1).hom) :
    (dgYonedaEquiv X F).symm x = yonedaNatTrans X F (LinearMap.mem_ker.1 x.2) :=
  (rfl)

/-- The transformation given by a closed element `x` of degree zero sends `g : Y ⟶ X` of degree
`p` to `F(g)(x)`. -/
@[simp]
theorem dgApp_dgYonedaEquiv_symm_v (x : LinearMap.ker ((F.obj (op X)).d 0 1).hom) {Y : C}
    {p : ℤ} (g : DGHom R p Y X) :
    ((((dgYonedaEquiv X F).symm x).dgApp (op Y) :
        Cochain ((dgRepresentable R X).obj (op Y)) (F.obj (op Y)) 0).v p p (add_zero p)).hom g =
      ((F.dgMap p (X := op X) (Y := op Y) g : Cochain (F.obj (op X)) (F.obj (op Y)) p).v 0 p
        (zero_add p)).hom x := by
  rw [dgYonedaEquiv_symm_apply, dgApp_dgYonedaNatTrans, yonedaApp_v, yonedaHom_f_apply]

/-! ### Transformations between representable modules -/

variable (R) in
/-- **DG natural transformations between representable modules** `Hom(-, X) ⟶ Hom(-, X')` are
the closed degree-zero morphisms `X ⟶ X'`: a transformation goes to the image of the identity
of `X`, and a closed morphism `u` goes to postcomposition with `u`
(`MathlibExt.DGSource.dgApp_dgRepresentableNatTransEquiv_symm_v`). -/
noncomputable def dgRepresentableNatTransEquiv (X X' : C) :
    DGNatTrans (dgRepresentable R X) (dgRepresentable R X') ≃ dgCycles R X X' :=
  (dgYonedaEquiv X (dgRepresentable R X')).trans
    (Equiv.subtypeEquivRight fun _ ↦ LinearMap.mem_ker.trans (mem_dgCycles R).symm)

/-- The closed morphism of a transformation between representable modules is the image of the
identity under its component at the source. -/
@[simp]
theorem dgRepresentableNatTransEquiv_apply_coe (X X' : C)
    (α : DGNatTrans (dgRepresentable R X) (dgRepresentable R X')) :
    (dgRepresentableNatTransEquiv R X X' α : DGHom R 0 X X') =
      ((α.dgApp (op X) : Cochain (dgHomComplex R X X) (dgHomComplex R X X') 0).v 0 0
        (add_zero 0)).hom (dgId R X) :=
  dgYonedaEquiv_apply_coe X _ α

/-- The transformation between representable modules given by a closed morphism `u : X ⟶ X'` is
postcomposition with `u`. -/
@[simp]
theorem dgApp_dgRepresentableNatTransEquiv_symm_v (X X' : C) (u : dgCycles R X X') {Y : C}
    {p : ℤ} (g : DGHom R p Y X) :
    ((((dgRepresentableNatTransEquiv R X X').symm u).dgApp (op Y) :
        Cochain (dgHomComplex R Y X) (dgHomComplex R Y X') 0).v p p (add_zero p)).hom g =
      dgComp R g (u : DGHom R 0 X X') (add_zero p) := by
  refine (dgApp_dgYonedaEquiv_symm_v X (dgRepresentable R X')
    ⟨u.1, LinearMap.mem_ker.2 ((mem_dgCycles R).1 u.2)⟩ g).trans ?_
  rw [dgRepresentable_dgMap]
  exact dgPrecomp_v R X' g 0 p (zero_add p) u.1

end Yoneda

end MathlibExt.DGSource
