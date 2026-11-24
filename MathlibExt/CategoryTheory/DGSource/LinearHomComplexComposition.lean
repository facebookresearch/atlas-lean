/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/LinearHomComplex/Composition.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.LinearHomComplex
public import MathlibExt.CategoryTheory.DGSource.CochainBraiding

/-!
# Composition of cochains as a morphism of `R`-linear Hom complexes

Composition of cochains is `R`-bilinear and satisfies the Leibniz rule

`δ (z₁.comp z₂) = z₁.comp (δ z₂) + (-1)^{|z₂|} • (δ z₁).comp z₂`

(Mathlib's `CochainComplex.HomComplex.δ_comp`; `Cochain.comp` is written in diagrammatic order, so
`z₁ : Cochain F G n₁` comes first and `z₂ : Cochain G K n₂` second).  Together these say exactly
that composition is a *closed degree-zero* map of `R`-linear Hom complexes, that is, a morphism

`linearHomComplex R G K ⊗ linearHomComplex R F G ⟶ linearHomComplex R F K`

in `CochainComplex (ModuleCat R) ℤ`.  The order of the two tensor factors is forced by the Koszul
sign rule: a morphism `φ` out of a tensor product of complexes is a chain map exactly when
`d (φ (x ⊗ y)) = φ (d x ⊗ y) + (-1)^{|x|} φ (x ⊗ d y)`, so the sign is carried by the term whose
differential hits the *second* factor.  In `δ_comp` the sign is carried by `(δ z₁).comp z₂`, the
term differentiating `z₁`; hence `z₁` must be the second tensor factor and `z₂` the first.  This
is Keller's `m₂ (g, f) = g ∘ f` convention.

Mathlib's `CategoryTheory.EnrichedCategory` instead asks for
`Hom(X, Y) ⊗ Hom(Y, Z) ⟶ Hom(X, Z)`; converting between the two orders is exactly the Koszul
braiding of `CochainComplex (ModuleCat R) ℤ`, built in
`MathlibExt/CategoryTheory/DGSource/CochainBraiding.lean` and imported here.  The `EnrichedCategory`
instance and its associativity and unit axioms in Mathlib's factor order are constructed in
`MathlibExt/CategoryTheory/DGSource/LinearHomComplexEnrichment.lean`.

The monoidal structure used here is Mathlib's `HomologicalComplex.monoidalCategory` at
`ComplexShape.up ℤ`; nothing is re-totalized.  The component equations for the whiskerings, the
unitors and the associator, which Mathlib does not state, are taken from
`MathlibExt/CategoryTheory/DGSource/CochainTensorSummands.lean` rather than repeated here.  Its
colimit-preservation hypotheses are discharged
by Mathlib's instances for a braided monoidal closed category, so
`Mathlib.CategoryTheory.Monoidal.Closed.Braided`, which that file imports, is what makes the
tensor product of cochain complexes exist at all.  Note that `ModuleCat.{v} R` is monoidal only for
a commutative `R : Type v`, so this file, unlike
`MathlibExt/CategoryTheory/DGSource/LinearHomComplex.lean`, requires `CommRing R` and ties the ring to
the morphism universe of `C`.

## Main definitions

* `MathlibExt.DGSource.linearHomComplexComp`: composition, as a morphism of `R`-linear Hom complexes out of
  the tensor product.
* `MathlibExt.DGSource.linearHomComplexOfHom`: a morphism of cochain complexes, as a degree-zero cocycle in
  the corresponding `R`-linear Hom complex.
* `MathlibExt.DGSource.linearHomComplexUnit`: the identity cochain, as a morphism from the tensor unit.

## Main results

* `MathlibExt.DGSource.ι_linearHomComplexComp`: the degree-`j` component restricted to a bidegree summand is
  `MathlibExt.DGSource.cochainCompTensor`; `MathlibExt.DGSource.cochainCompTensor_tmul` gives its pure-tensor formula.
* `MathlibExt.DGSource.linearHomComplexComp_naturality_source` and
  `MathlibExt.DGSource.linearHomComplexComp_naturality_target`: composition is natural in the source and in
  the target cochain complex.
* `MathlibExt.DGSource.linearHomComplexComp_dinaturality_middle`: composition is dinatural in the middle
  cochain complex.
* `MathlibExt.DGSource.linearHomComplexComp_assoc`, `MathlibExt.DGSource.linearHomComplexOfHom_comp`, and
  `MathlibExt.DGSource.linearHomComplexComp_ofHom`: composition is associative and composing with a
  degree-zero cocycle recovers postcomposition or precomposition; the unit laws are their identity
  specializations.
* `MathlibExt.DGSource.linearHomComplexOfHom_f_zero_apply`: a morphism of complexes gives its associated
  cochain in degree zero.

The Leibniz rule `δ_comp` and the totalized monoidal structure are supplied by Mathlib.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* B. Keller, *Deriving DG categories*, Section 1.
* Joël Riou's Mathlib cochain/`δ` and totalization API, together with the totalized
  `HomologicalComplex.monoidalCategory` of Joël Riou and Kim Morrison in
  `Mathlib/Algebra/Homology/Monoidal.lean`.  This file assembles Riou's `δ_comp` and the
  totalization API into the `ModuleCat R`-valued composition map, inheriting their sign convention.
-/

public section

open CategoryTheory Limits MonoidalCategory CochainComplex CochainComplex.HomComplex

namespace MathlibExt.DGSource

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  (F G K : CochainComplex C ℤ)

/-- Composition of a degree-`p` cochain from `G` to `K` with a degree-`q` cochain from `F` to `G`,
as a map out of the tensor product of the two cochain modules.  This is the bidegree-`(p, q)`
component of `MathlibExt.DGSource.linearHomComplexComp`. -/
noncomputable def cochainCompTensor (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    (linearHomComplex R G K).X p ⊗ (linearHomComplex R F G).X q ⟶
      (linearHomComplex R F K).X j :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (z₂ : Cochain G K p) (z₁ : Cochain F G q) => z₁.comp z₂ (by dsimp at h; omega))
    (fun _ _ _ => Cochain.comp_add _ _ _ _)
    (fun _ _ _ => Cochain.comp_smul _ _ _ _)
    (fun _ _ _ => Cochain.add_comp _ _ _ _)
    (fun _ _ _ => Cochain.smul_comp _ _ _ _)

/-- On a pure tensor, `cochainCompTensor` sends `z₂ ⊗ₜ z₁` to the composite `z₁.comp z₂`. -/
@[simp]
lemma cochainCompTensor_tmul (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j)
    (z₂ : ModuleCat.of R (Cochain G K p)) (z₁ : ModuleCat.of R (Cochain F G q)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom (cochainCompTensor R F G K p q j h) (z₂ ⊗ₜ z₁)) =
      (z₁.comp z₂ (by dsimp at h; omega) : ModuleCat.of R (Cochain F K j)) :=
  (rfl)

/- The expansion through `D₁` and `D₂` below is the unavoidable alignment between Mathlib's
totalized tensor differential and its bidegree inclusions.  Keeping it in this summand formula
isolates those implementation details from the chain-map construction. -/
private lemma cochainCompTensor_d (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
        (linearHomComplex R G K ⊗ linearHomComplex R F G).d j (j + 1) ≫
        HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · (j + 1) ·) =
      cochainCompTensor R F G K p q j h ≫ (linearHomComplex R F K).d j (j + 1) := by
  replace h : p + q = j := h
  have hd : (linearHomComplex R G K ⊗ linearHomComplex R F G).d j (j + 1) =
      HomologicalComplex.mapBifunctor.D₁ (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) +
        HomologicalComplex.mapBifunctor.D₂ (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) :=
    HomologicalComplex.mapBifunctor.d_eq _ _ _ _ j (j + 1)
  rw [hd, Preadditive.add_comp, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk p (p + 1) rfl) q (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (ComplexShape.up_mk q (q + 1) rfl) (j + 1) (by dsimp; omega),
    Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  let z₂' : ModuleCat.of R (Cochain G K p) := z₂
  let z₁' : ModuleCat.of R (Cochain F G q) := z₁
  simp only [curriedTensor_obj_obj, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ComplexShape.ε₁_def, curriedTensor_map_app, one_smul, ComplexShape.ε₂_def,
    ComplexShape.ε_up_ℤ, curriedTensor_obj_map, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.add_apply, ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  -- Express the totalized tensor differential on this pure tensor in the degreewise cochain
  -- modules characterized by `linearHomComplex_X`.
  change ModuleCat.Hom.hom (cochainCompTensor R F G K (p + 1) q (j + 1) _) (
        ModuleCat.Hom.hom ((linearHomComplex R G K).d p (p + 1)) z₂' ⊗ₜ z₁') +
      p.negOnePow • ModuleCat.Hom.hom (cochainCompTensor R F G K p (q + 1) (j + 1) _)
        (z₂' ⊗ₜ ModuleCat.Hom.hom ((linearHomComplex R F G).d q (q + 1)) z₁') =
    ModuleCat.Hom.hom ((linearHomComplex R F K).d j (j + 1))
      (ModuleCat.Hom.hom (cochainCompTensor R F G K p q j _) (z₂' ⊗ₜ z₁'))
  rw [linearHomComplex_d_hom_apply, linearHomComplex_d_hom_apply, cochainCompTensor_tmul,
    cochainCompTensor_tmul, cochainCompTensor_tmul, linearHomComplex_d_hom_apply]
  exact (δ_comp z₁' z₂' (by omega) (q + 1) (p + 1) (j + 1) rfl rfl rfl).symm

/-- **Composition of cochains is a closed degree-zero map.**  It assembles into a morphism of
cochain complexes of `R`-modules out of the tensor product; the differential of a composite is
computed by the Leibniz rule, which is precisely the condition for this to be a chain map. -/
noncomputable def linearHomComplexComp :
    linearHomComplex R G K ⊗ linearHomComplex R F G ⟶ linearHomComplex R F K where
  f j := HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·)
  comm' j j' hjj' := by
    replace hjj' : j + 1 = j' := hjj'
    subst hjj'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    exact (cochainCompTensor_d R F G K p q j h).symm

/-- The degree-`j` component of cochain composition is induced by its maps on the bidegree
summands of the totalized tensor product. -/
private lemma linearHomComplexComp_f (j : ℤ) :
    (linearHomComplexComp R F G K).f j =
      HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·) :=
  rfl

/-- The degree-`j` component of composition restricted to the bidegree-`(p, q)` summand is
`cochainCompTensor`; see `cochainCompTensor_tmul` for its value on pure tensors. -/
@[reassoc (attr := simp)]
lemma ι_linearHomComplexComp (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R G K) (linearHomComplex R F G)
        (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
      (linearHomComplexComp R F G K).f j = cochainCompTensor R F G K p q j h := by
  rw [linearHomComplexComp_f]
  apply HomologicalComplex.ι_mapBifunctorDesc

/-- A morphism of cochain complexes, regarded as a degree-zero cocycle in the corresponding
`R`-linear Hom complex. -/
noncomputable def linearHomComplexOfHom {F G : CochainComplex C ℤ} (φ : F ⟶ G) :
    𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ linearHomComplex R F G :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F G 0) (Cochain.ofHom φ)))
    (fun i _ => ModuleCat.hom_ext (LinearMap.ext fun r => by
      -- `mkHomFromSingle` has no evaluation lemma for its closure proof.  Unfold its
      -- `ModuleCat.ofHom` composite once; the characteristic `δ` lemmas then apply directly.
      change δ 0 i (r • Cochain.ofHom φ) = 0
      rw [δ_smul, δ_ofHom, smul_zero]))

/-- The degree-zero component of `linearHomComplexOfHom` as a morphism in `ModuleCat`. -/
lemma linearHomComplexOfHom_f_zero {F G : CochainComplex C ℤ} (φ : F ⟶ G) :
    (linearHomComplexOfHom R φ).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F G 0) (Cochain.ofHom φ)) :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The degree-zero component of `linearHomComplexOfHom` sends a scalar to that scalar multiple
of the associated cochain. -/
@[simp]
lemma linearHomComplexOfHom_f_zero_apply {F G : CochainComplex C ℤ} (φ : F ⟶ G) (r : R) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexOfHom R φ).f 0)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{v} R))).inv r)) =
      (r • Cochain.ofHom φ : ModuleCat.of R (Cochain F G 0)) := by
  rw [linearHomComplexOfHom_f_zero]
  -- `ModuleCat.hom_comp` does not expose application through `ModuleCat.ofHom` in the form
  -- expected by the two characteristic lemmas below.  Align that composite once; no
  -- implementation detail remains after the rewrites.
  change LinearMap.toSpanSingleton R (Cochain F G 0) (Cochain.ofHom φ)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{v} R))).hom
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{v} R))).inv r)) = r • Cochain.ofHom φ
  rw [Iso.inv_hom_id_apply, LinearMap.toSpanSingleton_apply]

/-- The identity cochain of `F`, as a morphism from the tensor unit to the `R`-linear Hom complex
of `F` with itself. -/
noncomputable def linearHomComplexUnit :
    𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ linearHomComplex R F F :=
  linearHomComplexOfHom R (𝟙 F)

/-- The unit is the degree-zero cocycle associated to the identity morphism. -/
lemma linearHomComplexUnit_def :
    linearHomComplexUnit R F = linearHomComplexOfHom R (𝟙 F) :=
  (rfl)

/-- The degree-zero component of the unit sends a scalar to the corresponding scalar multiple of
the identity cochain. -/
@[simp]
lemma linearHomComplexUnit_f_zero_apply (r : R) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexUnit R F).f 0)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{v} R))).inv r)) =
      (r • Cochain.ofHom (𝟙 F) : ModuleCat.of R (Cochain F F 0)) := by
  rw [linearHomComplexUnit_def, linearHomComplexOfHom_f_zero_apply]

/- Two maps out of a tensor product of linear Hom complexes agree when they agree on every pure
tensor of cochains.  This keeps the totalization and `ModuleCat` extensionality boilerplate out of
the naturality and unit calculations below. -/
private lemma linearHomComplexTensor_hom_ext
    {A B D E : CochainComplex C ℤ} {Z : CochainComplex (ModuleCat.{v} R) ℤ}
    {f g : linearHomComplex R A B ⊗ linearHomComplex R D E ⟶ Z}
    (h : ∀ (p q j : ℤ)
        (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (p, q) = j)
        (z₁ : ModuleCat.of R (Cochain A B p))
        (z₂ : ModuleCat.of R (Cochain D E q)),
      ModuleCat.Hom.hom
          (HomologicalComplex.ιMapBifunctor (linearHomComplex R A B)
              (linearHomComplex R D E) (curriedTensor (ModuleCat.{v} R))
              (ComplexShape.up ℤ) p q j hpq ≫ f.f j)
          (z₁ ⊗ₜ z₂) =
        ModuleCat.Hom.hom
          (HomologicalComplex.ιMapBifunctor (linearHomComplex R A B)
              (linearHomComplex R D E) (curriedTensor (ModuleCat.{v} R))
              (ComplexShape.up ℤ) p q j hpq ≫ g.f j)
          (z₁ ⊗ₜ z₂)) :
    f = g := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₁ z₂
  simpa only [linearHomComplex_X, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply] using h p q j hpq z₁ z₂

section Naturality

variable {F G K}
variable {F₁ F₂ G₁ G₂ K₁ K₂ : CochainComplex C ℤ}

/-- Composition is natural in the source: composing after precomposition by `φ` is the same as
precomposing the composite by `φ`.  This is associativity of `Cochain.comp` with the degree-zero
cochain `Cochain.ofHom φ` in the first (diagrammatic) argument. -/
@[reassoc]
lemma linearHomComplexComp_naturality_source (φ : F₁ ⟶ F₂) (G K : CochainComplex C ℤ) :
    linearHomComplex R G K ◁ linearHomComplexPrecomp R φ G ≫ linearHomComplexComp R F₁ G K =
      linearHomComplexComp R F₂ G K ≫ linearHomComplexPrecomp R φ K := by
  apply linearHomComplexTensor_hom_ext
  intro p q j h z₂ z₁
  have h' : p + q = j := h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex.whiskerLeft_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, Category.assoc,
    ι_linearHomComplexComp, ι_linearHomComplexComp_assoc]
  simp only [curriedTensor_obj_obj, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    NatTrans.id_app, curriedTensor_obj_map, Category.id_comp, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply]
  -- The totalization and tensor APIs provide the preceding morphism equations but no combined
  -- pure-tensor application lemma.  Align their `ModuleCat` wrappers with the advertised
  -- element-level APIs before rewriting.
  change ModuleCat.Hom.hom (cochainCompTensor R F₁ G K p q j h)
      (z₂ ⊗ₜ ModuleCat.Hom.hom ((linearHomComplexPrecomp R φ G).f q) z₁) =
    ModuleCat.Hom.hom ((linearHomComplexPrecomp R φ K).f j)
      (ModuleCat.Hom.hom (cochainCompTensor R F₂ G K p q j h) (z₂ ⊗ₜ z₁))
  rw [linearHomComplexPrecomp_f_apply, cochainCompTensor_tmul,
    cochainCompTensor_tmul, linearHomComplexPrecomp_f_apply]
  have hassoc : ((Cochain.ofHom φ).comp z₁ (zero_add q)).comp z₂ (by omega) =
      (Cochain.ofHom φ).comp (z₁.comp z₂ (by omega)) (zero_add j) :=
    Cochain.comp_assoc _ _ _ (zero_add q) (by omega) (by omega)
  exact hassoc

/-- Composition is natural in the target: composing after postcomposition by `ψ` is the same as
postcomposing the composite by `ψ`.  This is associativity of `Cochain.comp` with the degree-zero
cochain `Cochain.ofHom ψ` in the last (diagrammatic) argument. -/
@[reassoc]
lemma linearHomComplexComp_naturality_target (ψ : K₁ ⟶ K₂) (F G : CochainComplex C ℤ) :
    linearHomComplexPostcomp R G ψ ▷ linearHomComplex R F G ≫ linearHomComplexComp R F G K₂ =
      linearHomComplexComp R F G K₁ ≫ linearHomComplexPostcomp R F ψ := by
  apply linearHomComplexTensor_hom_ext
  intro p q j h z₂ z₁
  have h' : p + q = j := h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, Category.assoc,
    ι_linearHomComplexComp, ι_linearHomComplexComp_assoc]
  simp only [curriedTensor_obj_obj, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    curriedTensor_map_app, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ConcreteCategory.id_apply]
  -- The totalization and tensor APIs provide the preceding morphism equations but no combined
  -- pure-tensor application lemma.  Align their `ModuleCat` wrappers with the advertised
  -- element-level APIs before rewriting.
  change ModuleCat.Hom.hom (cochainCompTensor R F G K₂ p q j h)
      (ModuleCat.Hom.hom ((linearHomComplexPostcomp R G ψ).f p) z₂ ⊗ₜ z₁) =
    ModuleCat.Hom.hom ((linearHomComplexPostcomp R F ψ).f j)
      (ModuleCat.Hom.hom (cochainCompTensor R F G K₁ p q j h) (z₂ ⊗ₜ z₁))
  rw [linearHomComplexPostcomp_f_apply, cochainCompTensor_tmul,
    cochainCompTensor_tmul, linearHomComplexPostcomp_f_apply]
  have hassoc : (z₁.comp z₂ (by omega)).comp (Cochain.ofHom ψ) (add_zero j) =
      z₁.comp (z₂.comp (Cochain.ofHom ψ) (add_zero p)) (by omega) :=
    Cochain.comp_assoc _ _ _ (by omega) (add_zero p) (by omega)
  exact hassoc.symm

/-- Composition is dinatural in the middle object: precomposition in the first Hom complex agrees
with postcomposition in the second Hom complex. -/
@[reassoc]
lemma linearHomComplexComp_dinaturality_middle (ψ : G₁ ⟶ G₂) (F K : CochainComplex C ℤ) :
    linearHomComplexPrecomp R ψ K ▷ linearHomComplex R F G₁ ≫
        linearHomComplexComp R F G₁ K =
      linearHomComplex R G₂ K ◁ linearHomComplexPostcomp R F ψ ≫
        linearHomComplexComp R F G₂ K := by
  apply linearHomComplexTensor_hom_ext
  intro p q j h z₂ z₁
  have h' : p + q = j := h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc,
    HomologicalComplex.whiskerLeft_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_linearHomComplexComp, Category.assoc, ι_linearHomComplexComp]
  simp only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  -- The totalization and tensor APIs provide the preceding morphism equations but no combined
  -- pure-tensor application lemma.  Align their `ModuleCat` wrappers with the advertised
  -- element-level APIs before rewriting.
  change ModuleCat.Hom.hom (cochainCompTensor R F G₁ K p q j h)
      (ModuleCat.Hom.hom ((linearHomComplexPrecomp R ψ K).f p) z₂ ⊗ₜ z₁) =
    ModuleCat.Hom.hom (cochainCompTensor R F G₂ K p q j h)
      (z₂ ⊗ₜ ModuleCat.Hom.hom ((linearHomComplexPostcomp R F ψ).f q) z₁)
  rw [linearHomComplexPrecomp_f_apply, cochainCompTensor_tmul,
    linearHomComplexPostcomp_f_apply, cochainCompTensor_tmul]
  exact (Cochain.comp_assoc z₁ (Cochain.ofHom ψ) z₂ (add_zero q) (zero_add p) (by omega)).symm

end Naturality

section CategoryLaws

variable {F G K}
variable (L : CochainComplex C ℤ)

private lemma up_π_left_of_r (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (p + q, r) = j := by
  -- `ComplexShape.r` and `ComplexShape.π` are respectively a definition and an abbreviation;
  -- Mathlib has no named specialization reducing either one at `ComplexShape.up ℤ`.
  change p + q + r = j at h
  exact h

private lemma up_π_right_of_r (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (p, q + r) = j := by
  -- `ComplexShape.r` and `ComplexShape.π` are respectively a definition and an abbreviation;
  -- Mathlib has no named specialization reducing either one at `ComplexShape.up ℤ`.
  change p + q + r = j at h
  change p + (q + r) = j
  omega

/- Restrict the left-associated composite to a tridegree summand.  Factoring this calculation out
keeps the associativity proof focused on the resulting cochain equation. -/
private lemma ι₁₂_whiskerRight_comp (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
        (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) p q r j h ≫
      ((linearHomComplexComp R G K L ▷ linearHomComplex R F G) ≫
        linearHomComplexComp R F G L).f j =
    (cochainCompTensor R G K L p q (p + q) rfl ▷ (linearHomComplex R F G).X r) ≫
      cochainCompTensor R F G L (p + q) r j (up_π_left_of_r p q r j h) := by
  have h' : p + q + r = j := h
  rw [HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R))
      (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
      (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) p q r (p + q) j rfl (by omega),
    Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_linearHomComplexComp]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    curriedTensor_map_app, Category.id_comp]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ι_linearHomComplexComp]

/- Restrict the associator and right-associated composite to a tridegree summand. -/
private lemma ι₁₂_associator_whiskerLeft_comp (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
        (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) p q r j h ≫
      ((α_ (linearHomComplex R K L) (linearHomComplex R G K)
        (linearHomComplex R F G)).hom ≫
        (linearHomComplex R K L ◁ linearHomComplexComp R F G K) ≫
        linearHomComplexComp R F K L).f j =
    (α_ ((linearHomComplex R K L).X p) ((linearHomComplex R G K).X q)
      ((linearHomComplex R F G).X r)).hom ≫
      ((linearHomComplex R K L).X p ◁ cochainCompTensor R F G K q r (q + r) rfl) ≫
        cochainCompTensor R F K L p (q + r) j (up_π_right_of_r p q r j h) := by
  have h' : p + q + r = j := h
  -- The left-associated inclusion of a tridegree summand, in the whiskered form in which
  -- `HomologicalComplex.ι_ι_associator_hom` computes the associator.
  have e₁ : HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
      (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L) (linearHomComplex R G K)
      (linearHomComplex R F G) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j h =
      (HomologicalComplex.ιTensorObj (linearHomComplex R K L) (linearHomComplex R G K)
          p q (p + q) rfl ▷ (linearHomComplex R F G).X r) ≫
        HomologicalComplex.ιTensorObj (linearHomComplex R K L ⊗ linearHomComplex R G K)
          (linearHomComplex R F G) (p + q) r j h' := by
    rw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R))
      (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L) (linearHomComplex R G K)
      (linearHomComplex R F G) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r (p + q) j rfl
      (by omega)]
    rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, e₁, Category.assoc,
    HomologicalComplex.ι_ι_associator_hom_assoc _ _ _ p q r (p + q) (q + r) j rfl rfl h' (by omega),
    HomologicalComplex.ι_whiskerLeft_assoc,
    ι_linearHomComplexComp, ← MonoidalCategory.whiskerLeft_comp_assoc, ι_linearHomComplexComp]

/-- Composition of cochains is associative, with the tensor products identified by the monoidal
associator. -/
@[reassoc (attr := simp)]
lemma linearHomComplexComp_assoc :
    (linearHomComplexComp R G K L ▷ linearHomComplex R F G) ≫
        linearHomComplexComp R F G L =
      (α_ (linearHomComplex R K L) (linearHomComplex R G K)
        (linearHomComplex R F G)).hom ≫
        (linearHomComplex R K L ◁ linearHomComplexComp R F G K) ≫
          linearHomComplexComp R F K L := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = j := h
  rw [ι₁₂_whiskerRight_comp (R := R) (F := F) (G := G) (K := K) (L := L)
      (p := p) (q := q) (r := r) (j := j) (h := h),
    ι₁₂_associator_whiskerLeft_comp (R := R) (F := F) (G := G) (K := K) (L := L)
      (p := p) (q := q) (r := r) (j := j) (h := h)]
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro z₃ z₂ z₁
  let z₃' : ModuleCat.of R (Cochain K L p) := z₃
  let z₂' : ModuleCat.of R (Cochain G K q) := z₂
  let z₁' : ModuleCat.of R (Cochain F G r) := z₁
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  rw [ModuleCat.MonoidalCategory.associator_hom_apply z₃ z₂ z₁]
  rw [ModuleCat.MonoidalCategory.whiskerLeft_apply
      ((linearHomComplex R K L).X p) (cochainCompTensor R F G K q r (q + r) rfl)
      z₃ (z₂ ⊗ₜ z₁)]
  -- The three Mathlib application lemmas above leave nested tensor applications whose object
  -- types are expressed through `.X`.  Align those wrappers with `ModuleCat.of` so the public
  -- pure-tensor lemmas rewrite them without exposing `linearHomComplex`.
  change (ModuleCat.Hom.hom
      (cochainCompTensor R F G L (p + q) r j (up_π_left_of_r p q r j h))
      (ModuleCat.Hom.hom (cochainCompTensor R G K L p q (p + q) rfl)
          (z₃' ⊗ₜ z₂') ⊗ₜ z₁') : ModuleCat.of R (Cochain F L j)) =
    (ModuleCat.Hom.hom
      (cochainCompTensor R F K L p (q + r) j (up_π_right_of_r p q r j h))
      (z₃' ⊗ₜ ModuleCat.Hom.hom (cochainCompTensor R F G K q r (q + r) rfl)
        (z₂' ⊗ₜ z₁')) : ModuleCat.of R (Cochain F L j))
  rw [cochainCompTensor_tmul R G K L p q (p + q) rfl z₃' z₂',
    cochainCompTensor_tmul R F G L (p + q) r j (up_π_left_of_r p q r j h),
    cochainCompTensor_tmul R F G K q r (q + r) rfl z₂' z₁',
    cochainCompTensor_tmul R F K L p (q + r) j (up_π_right_of_r p q r j h)
      z₃' (z₁'.comp z₂' (by omega))]
  -- The preceding application lemmas leave only the proof arguments certifying the degree
  -- equalities; this alignment states the resulting cochain equation without wrapper casts.
  change z₁'.comp (z₂'.comp z₃' (by omega)) (by omega) =
    (z₁'.comp z₂' (by omega)).comp z₃' (by omega)
  exact (Cochain.comp_assoc (n₁₂ := q + r) (n₂₃ := p + q) (n₁₂₃ := j)
    z₁' z₂' z₃' (by omega) (by omega) (by omega)).symm

/-- Composing with the degree-zero cocycle associated to `ψ` is postcomposition by `ψ`. -/
@[reassoc]
lemma linearHomComplexOfHom_comp (ψ : G ⟶ K) :
    linearHomComplexOfHom R ψ ▷ linearHomComplex R F G ≫
        linearHomComplexComp R F G K =
      (λ_ (linearHomComplex R F G)).hom ≫ linearHomComplexPostcomp R F ψ := by
  apply (cancel_epi (λ_ (linearHomComplex R F G)).inv).1
  rw [Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.leftUnitor_inv_f, HomologicalComplex.leftUnitor'_inv]
  have hι :
      HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorUnit (ModuleCat.{v} R) (ComplexShape.up ℤ))
          (linearHomComplex R F G) 0 j j (zero_add j) ≫
        (linearHomComplexOfHom R ψ ▷ linearHomComplex R F G).f j ≫
          (linearHomComplexComp R F G K).f j =
        (linearHomComplexOfHom R ψ).f 0 ▷ (linearHomComplex R F G).X j ≫
          cochainCompTensor R F G K 0 j j (zero_add j) := by
    rw [HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
      HomologicalComplex.ι_mapBifunctorMap_assoc,
      ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [Category.assoc, Category.assoc, hι]
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  let z' : ModuleCat.of R (Cochain F G j) := z
  -- Mathlib has separate formulas for the unitor and whiskering applications but no formula for
  -- their resulting composite with a totalized bidegree map.  Align the remaining `.X` wrappers
  -- with the public `ModuleCat.of` application lemmas.
  change ModuleCat.Hom.hom (cochainCompTensor R F G K 0 j j (zero_add j))
      (ModuleCat.Hom.hom ((linearHomComplexOfHom R ψ).f 0)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat.{v} R))).inv 1) ⊗ₜ z') =
    ModuleCat.Hom.hom ((linearHomComplexPostcomp R F ψ).f j) z'
  rw [linearHomComplexOfHom_f_zero_apply, one_smul, cochainCompTensor_tmul,
    linearHomComplexPostcomp_f_apply]

/-- The identity cochain is a left unit for composition. -/
@[reassoc (attr := simp)]
lemma linearHomComplexUnit_comp :
    linearHomComplexUnit R G ▷ linearHomComplex R F G ≫
        linearHomComplexComp R F G G =
      (λ_ (linearHomComplex R F G)).hom := by
  simpa only [linearHomComplexUnit_def, linearHomComplexPostcomp_id, Category.comp_id] using
    linearHomComplexOfHom_comp (R := R) (F := F) (G := G) (K := G) (𝟙 G)

/-- Composing with the degree-zero cocycle associated to `φ` is precomposition by `φ`. -/
@[reassoc]
lemma linearHomComplexComp_ofHom {F' : CochainComplex C ℤ} (φ : F' ⟶ F) :
    linearHomComplex R F G ◁ linearHomComplexOfHom R φ ≫
        linearHomComplexComp R F' F G =
      (ρ_ (linearHomComplex R F G)).hom ≫ linearHomComplexPrecomp R φ G := by
  apply (cancel_epi (ρ_ (linearHomComplex R F G)).inv).1
  rw [Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.rightUnitor_inv_f, HomologicalComplex.rightUnitor'_inv]
  have hι :
      HomologicalComplex.ιTensorObj (linearHomComplex R F G)
          (HomologicalComplex.tensorUnit (ModuleCat.{v} R) (ComplexShape.up ℤ))
          j 0 j (add_zero j) ≫
        (linearHomComplex R F G ◁ linearHomComplexOfHom R φ).f j ≫
          (linearHomComplexComp R F' F G).f j =
        (linearHomComplex R F G).X j ◁ (linearHomComplexOfHom R φ).f 0 ≫
          cochainCompTensor R F' F G j 0 j (add_zero j) := by
    rw [HomologicalComplex.whiskerLeft_eq_mapBifunctorMap,
      HomologicalComplex.ι_mapBifunctorMap_assoc,
      ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.id_whiskerRight, Category.id_comp]
  rw [Category.assoc, Category.assoc, hι]
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  let z' : ModuleCat.of R (Cochain F G j) := z
  -- Mathlib has separate formulas for the unitor and whiskering applications but no formula for
  -- their resulting composite with a totalized bidegree map.  Align the remaining `.X` wrappers
  -- with the public `ModuleCat.of` application lemmas.
  change ModuleCat.Hom.hom (cochainCompTensor R F' F G j 0 j (add_zero j))
      (z' ⊗ₜ ModuleCat.Hom.hom ((linearHomComplexOfHom R φ).f 0)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{v} R))).inv 1)) =
    ModuleCat.Hom.hom ((linearHomComplexPrecomp R φ G).f j) z'
  rw [linearHomComplexOfHom_f_zero_apply, one_smul, cochainCompTensor_tmul,
    linearHomComplexPrecomp_f_apply]

/-- The identity cochain is a right unit for composition. -/
@[reassoc (attr := simp)]
lemma linearHomComplexComp_unit :
    linearHomComplex R F G ◁ linearHomComplexUnit R F ≫
        linearHomComplexComp R F F G =
      (ρ_ (linearHomComplex R F G)).hom := by
  simpa only [linearHomComplexUnit_def, linearHomComplexPrecomp_id, Category.comp_id] using
    linearHomComplexComp_ofHom (R := R) (F := F) (G := G) (F' := F) (𝟙 F)

end CategoryLaws

end MathlibExt.DGSource
