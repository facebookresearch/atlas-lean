/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Yoneda.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGFunctorCategory
public import MathlibExt.CategoryTheory.DGSource.DGQuasiEquivalence
public import MathlibExt.CategoryTheory.DGSource.DGRepresentables

/-!
# The DG Yoneda embedding of a DG category

For a small DG category `C` over `R`, the right DG modules over `C` are the DG functors
`Cᵒᵖ ⥤ C(R)` into cochain complexes, and they form a DG category whose Hom complexes consist of
the natural families of homogeneous morphisms (`MathlibExt.DGSource.DGFunctor.instDGCategory`).  This file
makes the representable modules `Hom(-, X)` of `MathlibExt.CategoryTheory.DGSource.DGRepresentables` into a DG
functor, the **DG Yoneda embedding** `MathlibExt.DGSource.dgYoneda : C ⥤ Mod-C`, and proves the Yoneda lemma
at the level of Hom complexes.

A morphism `u : X ⟶ X'` of degree `n` acts on `Hom(Y, X)` by postcomposition in Keller's order,
`g ↦ u ∘ g = (-1) ^ (p * n) • (g ≫ u)` for `g` of degree `p` (`MathlibExt.DGSource.dgPostcomp`).  With this
sign, postcomposition commutes with the differentials and with composition on the nose, and it
commutes with the precomposition action of `C` up to the Koszul sign `(-1) ^ (p * n)` demanded of
a natural family of degree `n` (`MathlibExt.DGSource.dgComp_dgMap_dgPostcomp`, in
`MathlibExt.CategoryTheory.DGSource.DGRepresentables`).

The **DG Yoneda lemma** identifies the Hom complex of modules `Hom(Hom(-, X), F)` with the
complex `F(X)`, by evaluating the component at `X` on the identity of `X`
(`MathlibExt.DGSource.dgRepresentableHomIso`).  The inverse sends `x` of degree `n` to the morphism whose
component at `Y` is `g ↦ (-1) ^ (p * n) • F(g)(x)`.  On closed degree-zero morphisms this is the
Yoneda bijection `MathlibExt.DGSource.dgYonedaEquiv` for DG natural transformations.  For a representable
target the inverse is postcomposition, so the Yoneda embedding is an isomorphism on every Hom
complex, and in particular quasi-fully faithful.

## Main definitions

* `MathlibExt.DGSource.dgPostcompHom`: postcomposition as a morphism of right DG modules
  `Hom(-, X) ⟶ Hom(-, X')`.
* `MathlibExt.DGSource.dgYoneda`: the DG Yoneda embedding.
* `MathlibExt.DGSource.dgRepresentableHomEquiv`: the degreewise Yoneda bijection between morphisms
  `Hom(-, X) ⟶ F` of degree `n` and elements of `F(X)` of degree `n`.
* `MathlibExt.DGSource.dgRepresentableHomIso`: the Yoneda isomorphism of complexes `Hom(Hom(-, X), F) ≅ F(X)`.

## Main results

* `MathlibExt.DGSource.isNatural_dgPostcomp`: postcompositions form a natural family.
* `MathlibExt.DGSource.dgYoneda_obj` and `MathlibExt.DGSource.dgYoneda_dgMap`: the Yoneda embedding sends `X` to
  `Hom(-, X)` and acts on morphisms by postcomposition.
* `MathlibExt.DGSource.dgRepresentableHomEquiv_dgDifferential`: the Yoneda bijection commutes with the
  differentials.
* `MathlibExt.DGSource.dgRepresentableHomEquiv_homEquivDGCycles`: on closed degree-zero morphisms it is
  `MathlibExt.DGSource.dgYonedaEquiv`.
* `MathlibExt.DGSource.isIso_map_dgYoneda`: the Yoneda embedding is an isomorphism on Hom complexes.
* `MathlibExt.DGSource.isQuasiFullyFaithful_dgYoneda`: the Yoneda embedding is quasi-fully faithful.

## References

* B. Keller, *Deriving DG categories*, Annales scientifiques de l'École Normale Supérieure 27
  (1994), Sections 1 and 2.
* G. M. Kelly, *Basic concepts of enriched category theory*, Sections 2.4 and 2.5, for the
  enriched Yoneda lemma and the full faithfulness of the enriched Yoneda embedding.
-/

public section

open CategoryTheory Opposite CochainComplex.HomComplex

namespace MathlibExt.DGSource

universe v u

variable (R : Type v) [CommRing R]

/-! ### Naturality of postcomposition -/

section Postcomp

variable {C : Type u} [DGCategory R C]

/-- **Postcomposition is natural**: for `u : X ⟶ X'` of degree `n`, the postcompositions with `u`
form a natural family of degree-`n` morphisms `Hom(-, X) ⟶ Hom(-, X')` of right DG modules. -/
theorem isNatural_dgPostcomp {X X' : C} {n : ℤ} (u : DGHom R n X X') :
    DGFunctor.IsNatural (F := ⟨dgRepresentable R X⟩) (G := ⟨dgRepresentable R X'⟩)
      fun Y ↦ dgPostcomp R Y n u := by
  refine DGFunctor.isNatural_iff.2 fun Y Z p f ↦ ?_
  exact dgComp_dgMap_dgPostcomp R f u rfl (add_comm n p)

end Postcomp

/-! ### The Yoneda embedding -/

section Embedding

variable {C : Type v} [DGCategory R C]

/-- **Postcomposition** with `u : X ⟶ X'` of degree `n`, as a degree-`n` morphism of right DG
modules `Hom(-, X) ⟶ Hom(-, X')`: its component at `Y` is `MathlibExt.DGSource.dgPostcomp`.  This is the action
of the Yoneda embedding on morphisms (`MathlibExt.DGSource.dgYoneda_dgMap`). -/
noncomputable def dgPostcompHom (X X' : C) (n : ℤ) :
    DGHom R n X X' →ₗ[R] DGHom R n
      (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ))
      ⟨dgRepresentable R X'⟩ :=
  (DGFunctor.dgHomEquiv R _ _ n).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (DGFunctor.natTransSubmodule _ _ n)
      (LinearMap.pi fun Y : Cᵒᵖ ↦ dgPostcomp R Y n)
      fun u ↦ DGFunctor.mem_natTransSubmodule.2 (isNatural_dgPostcomp R u)

/-- The component at `Y` of postcomposition with `u`, as a morphism of right DG modules, is
postcomposition with `u` on `Hom(Y, X)`. -/
@[simp]
theorem dgApp_dgPostcompHom {X X' : C} {n : ℤ} (u : DGHom R n X X') (Y : Cᵒᵖ) :
    DGFunctor.dgApp R n Y (dgPostcompHom R X X' n u) = dgPostcomp R Y n u :=
  DGFunctor.dgApp_dgHomEquiv_symm_apply R _ Y

/-- Postcomposition, as a morphism of right DG modules, commutes with the differentials. -/
@[simp]
theorem dgPostcompHom_dgDifferential {X X' : C} {n : ℤ} (u : DGHom R n X X') :
    dgPostcompHom R X X' (n + 1) (dgDifferential R n u) =
      dgDifferential R n (dgPostcompHom R X X' n u) :=
  DGFunctor.dgHom_ext R fun Y ↦ by
    rw [DGFunctor.dgApp_dgDifferential, dgApp_dgPostcompHom, dgApp_dgPostcompHom,
      dgPostcomp_dgDifferential]

/-- Postcomposition with an identity is the identity morphism of right DG modules. -/
@[simp]
theorem dgPostcompHom_dgId (X : C) :
    dgPostcompHom R X X 0 (dgId R X) =
      dgId R (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ)) :=
  DGFunctor.dgHom_ext R fun Y ↦ by
    rw [DGFunctor.dgApp_dgId, dgApp_dgPostcompHom, dgPostcomp_dgId]

/-- Postcomposition, as a morphism of right DG modules, is functorial. -/
@[simp]
theorem dgPostcompHom_dgComp {X X' X'' : C} {p q n : ℤ} (u : DGHom R p X X')
    (v : DGHom R q X' X'') (h : p + q = n) :
    dgPostcompHom R X X'' n (dgComp R u v h) =
      dgComp R (dgPostcompHom R X X' p u) (dgPostcompHom R X' X'' q v) h :=
  DGFunctor.dgHom_ext R fun Y ↦ by
    rw [DGFunctor.dgApp_dgComp, dgApp_dgPostcompHom, dgApp_dgPostcompHom, dgApp_dgPostcompHom,
      dgPostcomp_dgComp]

/-- The **DG Yoneda embedding** of a DG category `C` into the DG category of right DG modules over
`C`, the DG functors `Cᵒᵖ ⥤ C(R)`: an object `X` goes to the representable module `Hom(-, X)`, and
a morphism `u : X ⟶ X'` of degree `n` goes to the degree-`n` morphism of modules
`Hom(-, X) ⟶ Hom(-, X')` given by postcomposition with `u`, `g ↦ u ∘ g`
(`MathlibExt.DGSource.dgYoneda_dgMap`). -/
-- The body is exposed so that `(dgYoneda R).obj X` is definitionally the representable module
-- `Hom(-, X)`, as for `MathlibExt.DGSource.dgRepresentable`.
@[expose]
noncomputable def dgYoneda :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C
      (DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ)) :=
  EnrichedFunctor.ofDGMap (fun X ↦ ⟨dgRepresentable R X⟩) (fun {X X'} n ↦ dgPostcompHom R X X' n)
    (fun _ u ↦ dgPostcompHom_dgDifferential R u) (dgPostcompHom_dgId R)
    (fun u v h ↦ dgPostcompHom_dgComp R u v h)

/-- The Yoneda embedding sends an object `X` to the representable module `Hom(-, X)`. -/
@[simp]
theorem dgYoneda_obj (X : C) : (dgYoneda R).obj X = ⟨dgRepresentable R X⟩ :=
  (rfl)

/-- **The Yoneda embedding acts on morphisms by postcomposition.** -/
@[simp]
theorem dgYoneda_dgMap {X X' : C} {n : ℤ} (u : DGHom R n X X') :
    (dgYoneda R).dgMap n u = dgPostcompHom R X X' n u :=
  EnrichedFunctor.dgMap_ofDGMap (C := C)
    (fun X ↦ (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ)))
    (fun {X X'} n ↦ dgPostcompHom R X X' n) (fun _ u ↦ dgPostcompHom_dgDifferential R u)
    (dgPostcompHom_dgId R) (fun u v h ↦ dgPostcompHom_dgComp R u v h) n u

end Embedding

/-! ### The Yoneda lemma -/

section YonedaLemma

variable {C : Type v} [DGCategory R C] (X : C)
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) Cᵒᵖ
    (CochainComplex (ModuleCat.{v} R) ℤ))

/-- The cochain `Hom(Y, X) ⟶ F(Y)` of degree `n` given by an element `x` of `F(X)` of degree `n`,
sending `g : Y ⟶ X` of degree `p` to `(-1) ^ (p * n) • F(g)(x)`. -/
private noncomputable def yonedaCochainAux {n : ℤ} (x : (F.obj (op X)).X n) (Y : C) :
    Cochain (dgHomComplex R Y X) (F.obj (op Y)) n :=
  Cochain.mk fun p q hpq ↦ ModuleCat.ofHom <|
    (p * n).negOnePow • (cochainEval R x p q (by omega) ∘ₗ F.dgMap p (X := op X) (Y := op Y))

private theorem yonedaCochainAux_v {n : ℤ} (x : (F.obj (op X)).X n) (Y : C) (p q : ℤ)
    (hpq : p + n = q) (g : DGHom R p Y X) :
    ((yonedaCochainAux R X F x Y).v p q hpq).hom g =
      (p * n).negOnePow • ((F.dgMap p (X := op X) (Y := op Y) g :
        Cochain (F.obj (op X)) (F.obj (op Y)) p).v n q (by omega)).hom x :=
  congrArg ((p * n).negOnePow • ·)
    (cochainEval_apply R x p q (by omega) (F.dgMap p (X := op X) (Y := op Y) g))

private theorem dgPrecomp_comp_yonedaCochainAux {n : ℤ} (x : (F.obj (op X)).X n) {Y Z : C}
    {q m : ℤ} (f : DGHom R q Z Y) (h : q + n = m) (h' : n + q = m) :
    (dgPrecomp R X q f).comp (yonedaCochainAux R X F x Z) h =
      (q * n).negOnePow • (yonedaCochainAux R X F x Y).comp
        (F.dgMap q (X := op Y) (Y := op Z) f : Cochain (F.obj (op Y)) (F.obj (op Z)) q) h' := by
  refine Cochain.ext _ _ fun r s hrs ↦ ?_
  ext g
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ h r (r + q) s rfl (by omega),
    Cochain.comp_v _ _ h' r (r + n) s rfl (by omega)]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
    dgPrecomp_v, yonedaCochainAux_v]
  rw [dgMap_dgComp_v_apply X F f g (by omega) x (r + n) s (add_comm n r) (by omega),
    map_zsmul_unit, smul_smul]
  congr 1
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨0, by ring⟩

/-- The component at `Y` of the morphism of modules `Hom(-, X) ⟶ F` of degree `n` given by an
element `x` of `F(X)` of degree `n`. -/
private noncomputable def yonedaCochain {n : ℤ} (x : (F.obj (op X)).X n) (Y : Cᵒᵖ) :
    DGHom R n ((dgRepresentable R X).obj Y) (F.obj Y) :=
  yonedaCochainAux R X F x Y.unop

/-- The components of the morphism of modules `Hom(-, X) ⟶ F` of degree `n` given by an element
`x` of `F(X)` of degree `n` form a natural family. -/
private theorem isNatural_yonedaCochain {n : ℤ} (x : (F.obj (op X)).X n) :
    DGFunctor.IsNatural (F := ⟨dgRepresentable R X⟩) (G := ⟨F⟩) (yonedaCochain R X F x) := by
  refine DGFunctor.isNatural_iff.2 fun Y Z q f ↦ ?_
  rw [dgComp_linearHomComplex, dgComp_linearHomComplex]
  induction Y with | op Y => ?_
  induction Z with | op Z => ?_
  simp only [dgRepresentable_dgMap]
  -- The remaining `rfl` unfolds `yonedaCochain` to the cochain on Hom complexes.
  exact congrArg ((q * n).negOnePow • ·)
    ((dgPrecomp_comp_yonedaCochainAux R X F x f rfl (add_comm n q)).trans
      (by rw [mul_comm q n]; rfl))

/-- **A morphism of modules out of `Hom(-, X)` is determined by its value at the identity**: the
component at `Y` of a morphism `η` of degree `n` sends `g : Y ⟶ X` of degree `p` to
`(-1) ^ (p * n) • F(g)(η_X(1_X))`. -/
private theorem dgApp_v_apply {n : ℤ}
    (η : DGHom R n (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ))
      ⟨F⟩) {Y : C} {p q : ℤ} (g : DGHom R p Y X) (hpq : p + n = q) :
    ((DGFunctor.dgApp R n (op Y) η :
        Cochain ((dgRepresentable R X).obj (op Y)) (F.obj (op Y)) n).v p q hpq).hom g =
      (p * n).negOnePow • ((F.dgMap p (X := op X) (Y := op Y) g :
        Cochain (F.obj (op X)) (F.obj (op Y)) p).v n q (by omega)).hom
          (((DGFunctor.dgApp R n (op X) η :
            Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op X)) n).v 0 n
              (zero_add n)).hom (dgId R X)) := by
  -- Naturality of `η` against `g`, viewed as a morphism `op X ⟶ op Y`, evaluated on `1_X`, reads
  -- `(-1) ^ (p * n) • η_Y(g ≫ 1_X) = F(g)(η_X(1_X))`.  The equations are assembled with explicit
  -- transitivity because the components of `η` are typed by the representable module, whose
  -- values agree with the Hom complexes of `C` only after unfolding `dgRepresentable`.
  have k₁ := dgComp_v R ((dgRepresentable R X).dgMap p (X := op X) (Y := op Y) g)
    (DGFunctor.dgApp R n (op Y) η) hpq 0 p q (zero_add p) hpq
  have k₂ := dgComp_v R (DGFunctor.dgApp R n (op X) η) (F.dgMap p (X := op X) (Y := op Y) g)
    (by omega : n + p = q) 0 n q (zero_add n) (by omega)
  have key := congrArg (fun z : Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op Y)) q ↦
    z.v 0 q (by omega))
    (DGFunctor.dgComp_dgMap_dgApp R η (X := op X) (Y := op Y) g hpq (by omega))
  have key₂ := k₁.symm.trans (key.trans ((Cochain.units_smul_v _ _ 0 q _).trans
    (congrArg _ k₂)))
  rw [smul_smul, mul_comm n p, Int.units_mul_self, one_smul] at key₂
  have hg : (((dgRepresentable R X).dgMap p (X := op X) (Y := op Y) g :
      Cochain ((dgRepresentable R X).obj (op X)) ((dgRepresentable R X).obj (op Y)) p).v 0 p
        (zero_add p)).hom (dgId R X) = g := by
    rw [dgRepresentable_dgMap]
    exact (dgPrecomp_v R X g 0 p (zero_add p) (dgId R X)).trans (dgComp_dgId R g)
  refine (congrArg (ModuleCat.Hom.hom ((DGFunctor.dgApp R n (op Y) η :
    Cochain ((dgRepresentable R X).obj (op Y)) (F.obj (op Y)) n).v p q hpq)) hg).symm.trans ?_
  refine Eq.trans ?_
    (congrArg (fun φ ↦ (p * n).negOnePow • ModuleCat.Hom.hom φ (dgId R X)) key₂)
  have hsmul {M N : ModuleCat.{v} R} (u : ℤˣ) (φ : M ⟶ N) (y : M) :
      (u • φ).hom y = u • φ.hom y := rfl
  refine Eq.trans ?_ (congrArg ((p * n).negOnePow • ·) (hsmul _ _ _).symm)
  rw [smul_smul, Int.units_mul_self, one_smul]
  rfl

/-- **The DG Yoneda lemma**, degreewise: morphisms of degree `n` of right DG modules
`Hom(-, X) ⟶ F` are the elements of `F(X)` of degree `n`.  A morphism `η` goes to `η_X(1_X)`
(`MathlibExt.DGSource.dgRepresentableHomEquiv_apply`), and an element `x` goes to the morphism whose component
at `Y` sends `g : Y ⟶ X` of degree `p` to `(-1) ^ (p * n) • F(g)(x)`
(`MathlibExt.DGSource.dgApp_dgRepresentableHomEquiv_symm_v`). -/
noncomputable def dgRepresentableHomEquiv (n : ℤ) :
    DGHom R n (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ))
      ⟨F⟩ ≃ₗ[R] (F.obj (op X)).X n where
  toLinearMap :=
    cochainEval R (K := (dgRepresentable R X).obj (op X)) (dgId R X) n n (zero_add n) ∘ₗ
      DGFunctor.dgApp R n (op X)
  invFun x := (DGFunctor.dgHomEquiv R _ _ n).symm
    ⟨yonedaCochain R X F x, DGFunctor.mem_natTransSubmodule.2 (isNatural_yonedaCochain R X F x)⟩
  left_inv η := DGFunctor.dgHom_ext R fun Y ↦ by
    dsimp only
    rw [DGFunctor.dgApp_dgHomEquiv_symm_apply]
    induction Y with | op Y => ?_
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (g : DGHom R p Y X) ↦ ?_)
    refine (yonedaCochainAux_v R X F _ Y p q hpq g).trans
      (Eq.trans ?_ (dgApp_v_apply R X F η g hpq).symm)
    exact congrArg (fun y ↦ (p * n).negOnePow • ((F.dgMap p (X := op X) (Y := op Y) g :
      Cochain (F.obj (op X)) (F.obj (op Y)) p).v n q (by omega)).hom y)
        (cochainEval_apply R (K := (dgRepresentable R X).obj (op X)) (dgId R X) n n (zero_add n) _)
  right_inv x := by
    have hF : (F.dgMap 0 (X := op X) (Y := op X) (dgId R X) :
        Cochain (F.obj (op X)) (F.obj (op X)) 0) = Cochain.ofHom (𝟙 _) := by
      rw [← dgId_op, F.dgMap_dgId, dgId_linearHomComplex]
    refine (congrArg (cochainEval R (K := (dgRepresentable R X).obj (op X)) (dgId R X) n n
      (zero_add n)) (DGFunctor.dgApp_dgHomEquiv_symm_apply R (F := ⟨dgRepresentable R X⟩)
        (G := ⟨F⟩) ⟨yonedaCochain R X F x,
          DGFunctor.mem_natTransSubmodule.2 (isNatural_yonedaCochain R X F x)⟩ (op X))).trans ?_
    refine (cochainEval_apply R (dgId R X) n n (zero_add n) _).trans ?_
    refine (yonedaCochainAux_v R X F x X 0 n (zero_add n) (dgId R X)).trans ?_
    rw [hF, zero_mul, Int.negOnePow_zero, one_smul, Cochain.ofHom_v, HomologicalComplex.id_f,
      ModuleCat.id_apply]

/-- The Yoneda bijection sends a morphism `η : Hom(-, X) ⟶ F` to `η_X(1_X)`. -/
@[simp]
theorem dgRepresentableHomEquiv_apply {n : ℤ}
    (η : DGHom R n (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ))
      ⟨F⟩) :
    dgRepresentableHomEquiv R X F n η =
      ((DGFunctor.dgApp R n (op X) η :
        Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op X)) n).v 0 n (zero_add n)).hom
        (dgId R X) :=
  cochainEval_apply R (K := (dgRepresentable R X).obj (op X)) (dgId R X) n n (zero_add n) _

/-- The morphism `Hom(-, X) ⟶ F` given by an element `x` of `F(X)` of degree `n` sends
`g : Y ⟶ X` of degree `p` to `(-1) ^ (p * n) • F(g)(x)`. -/
@[simp]
theorem dgApp_dgRepresentableHomEquiv_symm_v {n : ℤ} (x : (F.obj (op X)).X n) {Y : C} {p q : ℤ}
    (hpq : p + n = q) (g : DGHom R p Y X) :
    ((DGFunctor.dgApp R n (op Y) ((dgRepresentableHomEquiv R X F n).symm x) :
        Cochain ((dgRepresentable R X).obj (op Y)) (F.obj (op Y)) n).v p q hpq).hom g =
      (p * n).negOnePow • ((F.dgMap p (X := op X) (Y := op Y) g :
        Cochain (F.obj (op X)) (F.obj (op Y)) p).v n q (by omega)).hom x :=
  (congrArg (fun z : Cochain ((dgRepresentable R X).obj (op Y)) (F.obj (op Y)) n ↦
    (z.v p q hpq).hom g) (DGFunctor.dgApp_dgHomEquiv_symm_apply R (F := ⟨dgRepresentable R X⟩)
      (G := ⟨F⟩) ⟨yonedaCochain R X F x,
        DGFunctor.mem_natTransSubmodule.2 (isNatural_yonedaCochain R X F x)⟩ (op Y))).trans
    (yonedaCochainAux_v R X F x Y p q hpq g)

/-- **The Yoneda bijection commutes with the differentials**: the value at the identity of the
differential of `η` is the differential of the value of `η` at the identity. -/
theorem dgRepresentableHomEquiv_dgDifferential {n : ℤ}
    (η : DGHom R n (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ))
      ⟨F⟩) :
    dgRepresentableHomEquiv R X F (n + 1) (dgDifferential R n η) =
      ((F.obj (op X)).d n (n + 1)).hom (dgRepresentableHomEquiv R X F n η) :=
  (dgRepresentableHomEquiv_apply R X F _).trans <|
    ((congrArg (fun z : Cochain ((dgRepresentable R X).obj (op X)) (F.obj (op X)) (n + 1) ↦
      (z.v 0 (n + 1) (zero_add _)).hom (dgId R X))
        ((DGFunctor.dgApp_dgDifferential R η (op X)).trans
          (dgDifferential_linearHomComplex R n (DGFunctor.dgApp R n (op X) η)))).trans
      (δ_v_apply_of_d_eq_zero (DGFunctor.dgApp R n (op X) η) (zero_add n) (zero_add _)
        (dgDifferential_dgId R X))).trans
      (congrArg ((F.obj (op X)).d n (n + 1)).hom (dgRepresentableHomEquiv_apply R X F η).symm)

/-- **The DG Yoneda lemma**: evaluation at the identity of `X` is an isomorphism from the Hom
complex of right DG modules `Hom(Hom(-, X), F)` to the complex `F(X)`. -/
noncomputable def dgRepresentableHomIso :
    dgHomComplex R (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ))
      ⟨F⟩ ≅ F.obj (op X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (dgRepresentableHomEquiv R X F n).toModuleIso)
    fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      ext η
      exact (dgRepresentableHomEquiv_dgDifferential R X F η).symm

/-- The degree-`n` component of the Yoneda isomorphism is the Yoneda bijection. -/
@[simp]
theorem dgRepresentableHomIso_hom_f_apply {n : ℤ}
    (η : DGHom R n (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ))
      ⟨F⟩) :
    ((dgRepresentableHomIso R X F).hom.f n).hom η = dgRepresentableHomEquiv R X F n η :=
  (rfl)

/-- On closed degree-zero morphisms the Yoneda bijection is the Yoneda bijection
`MathlibExt.DGSource.dgYonedaEquiv` for DG natural transformations. -/
theorem dgRepresentableHomEquiv_homEquivDGCycles
    (α : (⟨dgRepresentable R X⟩ : DGFunctor R Cᵒᵖ (CochainComplex (ModuleCat.{v} R) ℤ)) ⟶ ⟨F⟩) :
    dgRepresentableHomEquiv R X F 0 (DGFunctor.homEquivDGCycles R _ _ α : DGHom R 0 _ _) =
      (dgYonedaEquiv X F α : (F.obj (op X)).X 0) := by
  rw [dgRepresentableHomEquiv_apply, DGFunctor.dgApp_homEquivDGCycles_apply,
    dgYonedaEquiv_apply_coe, DGNatTrans.dgApp_eq_dgClosedHom]

end YonedaLemma

/-! ### Full faithfulness of the Yoneda embedding -/

section FullyFaithful

variable {C : Type v} [DGCategory R C]

/-- The value at the identity of postcomposition with `u` is `u`. -/
theorem dgRepresentableHomEquiv_dgPostcompHom {X X' : C} {n : ℤ} (u : DGHom R n X X') :
    dgRepresentableHomEquiv R X (dgRepresentable R X') n (dgPostcompHom R X X' n u) = u :=
  (dgRepresentableHomEquiv_apply R X _ _).trans <|
    (congrArg (fun z : Cochain ((dgRepresentable R X).obj (op X))
      ((dgRepresentable R X').obj (op X)) n ↦ (z.v 0 n (zero_add n)).hom (dgId R X))
        (dgApp_dgPostcompHom R u (op X))).trans <|
    (dgPostcomp_v R X u 0 n (zero_add n) (dgId R X)).trans <| by
      rw [zero_mul, Int.negOnePow_zero, one_smul, dgId_dgComp]

/-- Postcomposition is a bijection from morphisms `X ⟶ X'` of degree `n` to morphisms of right
DG modules `Hom(-, X) ⟶ Hom(-, X')` of degree `n`, inverse to the Yoneda bijection. -/
private theorem bijective_dgPostcompHom (X X' : C) (n : ℤ) :
    Function.Bijective (dgPostcompHom R X X' n) :=
  ⟨fun u u' h ↦ (dgRepresentableHomEquiv_dgPostcompHom R u).symm.trans
      ((congrArg (dgRepresentableHomEquiv R X (dgRepresentable R X') n) h).trans
        (dgRepresentableHomEquiv_dgPostcompHom R u')),
    fun η ↦ ⟨dgRepresentableHomEquiv R X (dgRepresentable R X') n η,
      (dgRepresentableHomEquiv R X (dgRepresentable R X') n).injective
        (dgRepresentableHomEquiv_dgPostcompHom R _)⟩⟩

/-- **The DG Yoneda embedding is fully faithful**: it is an isomorphism on every Hom complex. -/
theorem isIso_map_dgYoneda (X X' : C) : IsIso ((dgYoneda R).map X X') := by
  have (n : ℤ) : IsIso (((dgYoneda R).map X X').f n) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have e : ⇑(((dgYoneda R).map X X').f n) = dgPostcompHom R X X' n :=
      funext fun u ↦ (EnrichedFunctor.dgMap_apply _ u).symm.trans (dgYoneda_dgMap R u)
    rw [e]
    exact bijective_dgPostcompHom R X X' n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The DG Yoneda embedding is quasi-fully faithful. -/
theorem isQuasiFullyFaithful_dgYoneda : (dgYoneda (C := C) R).IsQuasiFullyFaithful :=
  EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map (isIso_map_dgYoneda R)

end FullyFaithful

end MathlibExt.DGSource
