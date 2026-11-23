/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTwoOfThree
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MappingPathTarget

/-!
# Kan homotopy pullbacks via mapping path spaces

This file develops the Kan homotopy-pullback yoga (Joyal R4', item Y2,
Kerodon §3.4.1-analogs) in a self-contained way from mapping path spaces,
without any model structure on `SSet`, long exact sequences, or contraction
homotopies:

* Step 1: the endpoint evaluation `eval₀ : pathSpace B ⟶ B` has the right
  lifting property against all boundary inclusions (`I.rlp`) for Kan `B`.
  By exponential adjunction, a boundary-lifting problem against the
  pullback-hom transposes to lifting the pushout-product
  `(∂Δ[n] ↪ Δ[n]) □ ({0} ↪ Δ[1])` against `B`; the pushout-product is
  anodyne because `{0} ↪ Δ[1]` is the horn `Λ[1,0] ↪ Δ[1]`
  (`SSet.anodyneExtensions_pushoutObjObjι'`).
* Step 2: the mapping path space `M_f = X ×_B pathSpace B`
  (`SSet.mappingPathSpace`, from `SSetDeformationRetract.lean`) factors
  `f = section ≫ target` with the retract in `I.rlp` (hence in `W` by
  `KanComplex.W.of_rlp_I`, so the section is in `W` by 2-of-3) and the
  target map `M_f ⟶ B` a Kan fibration (it factors through a pullback of
  `evalPair`).
* Step 3: `SSet.IsKanHomotopyPullback` over Kan cospans (comparison into the
  single mapping-path-space replacement of the right leg), with
  `SSet.homotopyPullback_twoOfThree` for maps of squares (formal from `W`
  2-of-3, plus a homotopy-transfer corollary from `W.iff_of_homotopy`),
  right-leg weak-equivalence transfer, and the strict-pullback case along a
  trivial Kan fibration.

B2-free audit: no step strictifies `h`-data or corrects simplices. All
arguments are lifting properties (exponential adjunction, base-change
stability of `rlp` classes), pullback pasting/universal properties, and
2-of-3 bookkeeping for `KanComplex.W`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Simplicial SSet HomotopicalAlgebra Limits
open SSet.modelCategoryQuillen

universe u

namespace SSet

/-! ## Step 1: `eval₀` has boundary RLP

The vertex inclusion `{0} ↪ Δ[1]` is the horn `Λ[1,0]`, hence anodyne;
the pullback-hom/exponential adjunction turns boundary lifting against
`eval₀` into anodyne lifting against the Kan complex `B`.
-/

/-- The face `{0}` of `Δ[1]` is the horn `Λ[1,0]`, by direct inspection of
the horn as a union of faces. -/
private theorem face_zero_eq_horn_one_zero :
    stdSimplex.face ({0} : Finset (Fin 2)) = horn (1 : ℕ) (0 : Fin 2) := by
  have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
  calc stdSimplex.face ({0} : Finset (Fin 2))
      = stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
    _ = horn (1 : ℕ) (0 : Fin 2) := by
        ext m x
        simp [horn_eq_iSup]

/-- The vertex inclusion `{0} ↪ Δ[1]` is an anodyne extension: it is the
horn `Λ[1,0] ↪ Δ[1]` up to the canonical face iso. -/
private theorem anodyneExtensions_stdSimplex_δ_one :
    anodyneExtensions (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have h_eq : stdSimplex.face ({1}ᶜ : Finset (Fin 2)) = horn (1 : ℕ) (0 : Fin 2) := by
    have h_fin : ({1}ᶜ : Finset (Fin 2)) = {0} := by decide
    rw [h_fin]
    exact face_zero_eq_horn_one_zero
  let e : Arrow.mk (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≅
      Arrow.mk (horn (1 : ℕ) (0 : Fin 2)).ι :=
    Arrow.isoMk
      (stdSimplex.faceSingletonComplIso (1 : Fin 2) ≪≫ Subcomplex.eqToIso h_eq)
      (Iso.refl _) (by
        change (stdSimplex.faceSingletonComplIso (1 : Fin 2) ≪≫
            Subcomplex.eqToIso h_eq).hom ≫ (horn 1 (0 : Fin 2)).ι =
          stdSimplex.δ (1 : Fin 2) ≫ (Iso.refl _).hom
        simp only [Iso.trans_hom, Category.assoc, Subcomplex.eqToIso_hom,
          Subcomplex.homOfLE_ι, stdSimplex.faceSingletonComplIso_hom_ι,
          Iso.refl_hom, Category.comp_id])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left e p]
  exact anodyneExtensions.horn_ι (0 : Fin 2) p hp

/-- The pullback-hom `(pre {0}↪Δ[1]).app B` has boundary RLP for Kan `B`:
by exponential adjunction this is lifting the anodyne pushout-product
`(∂Δ[n] ↪ Δ[n]) □ ({0} ↪ Δ[1])` against `B`. -/
private theorem I_rlp_pre_δ_one_app {B : SSet.{u}} [KanComplex B] :
    I.rlp ((MonoidalClosed.pre
      (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app B) := by
  intro _ _ _ hg
  obtain ⟨n⟩ := hg
  let sq₁₃ := Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])
    (terminal.from B) terminalIsTerminal
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) (boundary n).ι
  change HasLiftingProperty (boundary n).ι sq₁₃.π
  rw [← MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂ sq₁₃]
  have han := anodyneExtensions_pushoutObjObjι' sq₁₂
    anodyneExtensions_stdSimplex_δ_one
  have hFibB : Fibration (terminal.from B) := ‹KanComplex B›
  exact han _ ((HomotopicalAlgebra.fibration_iff (terminal.from B)).1 hFibB)

/-- Endpoint evaluation at `0` has the right lifting property against all
boundary inclusions for Kan `B`: it is the pullback-hom above followed by
the `ihom Δ[0] ≅ id` isomorphism. -/
theorem eval₀_mem_I_rlp {B : SSet.{u}} [KanComplex B] :
    I.rlp (eval₀ (X := B)) := by
  have h_pre := I_rlp_pre_δ_one_app (B := B)
  have h_eval₀ := eval₀_eq_pre_app B
  let e : Arrow.mk (eval₀ (X := B)) ≅
      Arrow.mk ((MonoidalClosed.pre
        (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app B) :=
    Arrow.isoMk (Iso.refl _) (ihomZeroIso B).symm (by
      change (MonoidalClosed.pre
          (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app B =
        (eval₀ (X := B)) ≫ (ihomZeroIso B).symm.hom
      rw [h_eval₀, Category.assoc, Iso.symm_hom, Iso.hom_inv_id,
        Category.comp_id])
  intro X Y g hg
  rw [HasLiftingProperty.iff_of_arrow_iso_right g e]
  exact h_pre _ hg

/-! ## Step 2: homotopical properties of the mapping path space

The mapping path space `M_f`, its section, retract, and path evaluation
are from `SSetDeformationRetract.lean`. Here we add the target map
`M_f ⟶ B` (evaluation at the far endpoint), the factorization
`f = section ≫ target`, boundary RLP of the retract, weak equivalences,
and Kan-fibration properties.
-/

/-- Pullback of a Kan fibration is a Kan fibration: base-change stability
of `J.rlp`, via the general `rlp` stability upstream. -/
theorem fibration_of_isPullback {P X Y S : SSet.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (sq : IsPullback fst snd f g) [Fibration g] :
    Fibration fst := by
  have hg : J.rlp g := (modelCategoryQuillen.fibration_iff g).1 ‹Fibration g›
  have hf : J.rlp fst := MorphismProperty.of_isPullback sq.flip hg
  exact (modelCategoryQuillen.fibration_iff fst).2 hf

/-- The canonical first projection of a pullback of a Kan fibration is a
Kan fibration. -/
instance fibration_pullback_fst {X E B : SSet.{u}} {f : X ⟶ B} {p : E ⟶ B}
    [Fibration p] : Fibration (pullback.fst f p) :=
  fibration_of_isPullback (IsPullback.of_hasPullback f p)

/-- The pullback of a Kan fibration over a Kan complex is Kan. -/
instance kanComplex_pullback_of_fibration {X E B : SSet.{u}} {f : X ⟶ B}
    {p : E ⟶ B} [Fibration p] [KanComplex X] : KanComplex (pullback f p) :=
  isFibrant_of_fibration (pullback.fst f p)

/-- The mapping-path-space retract is a Kan fibration: it pulls back
`eval₀`. -/
instance {X B : SSet.{u}} (f : X ⟶ B) [KanComplex B] :
    Fibration (mappingPathRetract f) :=
  fibration_of_isPullback (IsPullback.of_hasPullback f eval₀)

/-- The mapping path space over Kan ends is Kan. -/
instance {X B : SSet.{u}} (f : X ⟶ B) [KanComplex X] [KanComplex B] :
    KanComplex (mappingPathSpace (f := f)) :=
  isFibrant_of_fibration (mappingPathRetract f)

/-- The mapping-path-space retract has boundary RLP: it pulls back
`eval₀`. -/
theorem mappingPathRetract_mem_I_rlp {X B : SSet.{u}} (f : X ⟶ B)
    [KanComplex B] : I.rlp (mappingPathRetract f) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback f eval₀).flip
    (eval₀_mem_I_rlp (B := B))

/-- The mapping-path-space retract is a weak equivalence. -/
theorem KanComplex.W.of_mappingPathRetract {X B : SSet.{u}} (f : X ⟶ B)
    [KanComplex X] [KanComplex B] : KanComplex.W (mappingPathRetract f) :=
  KanComplex.W.of_rlp_I (mappingPathRetract_mem_I_rlp f)

/-- The mapping-path-space section is a weak equivalence: it is a section
of the retract, which is a weak equivalence. -/
theorem KanComplex.W.of_mappingPathSection {X B : SSet.{u}} (f : X ⟶ B)
    [KanComplex X] [KanComplex B] : KanComplex.W (mappingPathSection f) := by
  have hπ := KanComplex.W.of_mappingPathRetract f
  have hid : KanComplex.W (mappingPathSection f ≫ mappingPathRetract f) := by
    rw [mappingPathSection_comp_retract]
    exact KanComplex.W.id
  exact KanComplex.W.of_postcomp hπ hid

/-! ## The target map is a Kan fibration

The map `(retract, target) : M_f ⟶ X ⊗ B` is a pullback of `evalPair`
along `f × id`, hence a Kan fibration; the target map `M_f ⟶ B` is its
composite with the second projection (a Kan fibration for Kan `X`).
-/

/-- The map `(retract, target) : M_f ⟶ X ⊗ B` into the product, stated
in pullback-native form so all rewriting below is syntactic. -/
private noncomputable def mappingPathProdLift {X B : SSet.{u}} (f : X ⟶ B) :
    pullback f eval₀ ⟶ X ⊗ B :=
  CartesianMonoidalCategory.lift (pullback.fst f eval₀)
    (pullback.snd f eval₀ ≫ eval₁)

/-- The map `f × id : X ⊗ B ⟶ B ⊗ B` on products. -/
private noncomputable def mappingPathProdMap {X B : SSet.{u}} (f : X ⟶ B) :
    X ⊗ B ⟶ B ⊗ B :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst X B ≫ f) (CartesianMonoidalCategory.snd X B)

private theorem mappingPathProdMap_fst {X B : SSet.{u}} (f : X ⟶ B) :
    mappingPathProdMap f ≫ CartesianMonoidalCategory.fst B B =
      CartesianMonoidalCategory.fst X B ≫ f :=
  CartesianMonoidalCategory.lift_fst _ _

private theorem mappingPathProdMap_snd {X B : SSet.{u}} (f : X ⟶ B) :
    mappingPathProdMap f ≫ CartesianMonoidalCategory.snd B B =
      CartesianMonoidalCategory.snd X B :=
  CartesianMonoidalCategory.lift_snd _ _

private theorem mappingPathProdLift_fst {X B : SSet.{u}} (f : X ⟶ B) :
    mappingPathProdLift f ≫ CartesianMonoidalCategory.fst X B =
      pullback.fst f eval₀ :=
  CartesianMonoidalCategory.lift_fst _ _

private theorem mappingPathProdLift_snd {X B : SSet.{u}} (f : X ⟶ B) :
    mappingPathProdLift f ≫ CartesianMonoidalCategory.snd X B =
      pullback.snd f eval₀ ≫ eval₁ :=
  CartesianMonoidalCategory.lift_snd _ _

/-- The product square over `evalPair` commutes. -/
private theorem mappingPathProd_comm {X B : SSet.{u}} (f : X ⟶ B) :
    mappingPathProdLift f ≫ mappingPathProdMap f =
      pullback.snd f eval₀ ≫ evalPair := by
  apply CartesianMonoidalCategory.hom_ext
  · calc (mappingPathProdLift f ≫ mappingPathProdMap f) ≫
          CartesianMonoidalCategory.fst B B
        = pullback.fst f eval₀ ≫ f := by
          rw [Category.assoc, mappingPathProdMap_fst, ← Category.assoc,
            mappingPathProdLift_fst]
      _ = pullback.snd f eval₀ ≫ eval₀ := pullback.condition
      _ = (pullback.snd f eval₀ ≫ evalPair) ≫
          CartesianMonoidalCategory.fst B B := by
          rw [Category.assoc, evalPair_fst]
  · calc (mappingPathProdLift f ≫ mappingPathProdMap f) ≫
          CartesianMonoidalCategory.snd B B
        = pullback.snd f eval₀ ≫ eval₁ := by
          rw [Category.assoc, mappingPathProdMap_snd, mappingPathProdLift_snd]
      _ = (pullback.snd f eval₀ ≫ evalPair) ≫
          CartesianMonoidalCategory.snd B B := by
          rw [Category.assoc, evalPair_snd]

/-- The product square over `evalPair` is a pullback: an element of the
pullback is `(x, b, γ)` with `γ(0) = f(x)` and `γ(1) = b`, so `b` is
forced and `(x, γ)` is free in `M_f`. -/
private theorem isPullback_mappingPathProd {X B : SSet.{u}} (f : X ⟶ B) :
    IsPullback (mappingPathProdLift f) (pullback.snd f eval₀)
      (mappingPathProdMap f) evalPair where
  w := mappingPathProd_comm f
  isLimit' := by
    have liftW : ∀ s : PullbackCone (mappingPathProdMap f) evalPair,
        (s.fst ≫ CartesianMonoidalCategory.fst X B) ≫ f = s.snd ≫ eval₀ := by
      intro s
      have hfst : (s.fst ≫ mappingPathProdMap f) ≫
            CartesianMonoidalCategory.fst B B =
          (s.snd ≫ evalPair) ≫ CartesianMonoidalCategory.fst B B := by
        rw [s.condition]
      rw [Category.assoc, mappingPathProdMap_fst, Category.assoc,
        evalPair_fst] at hfst
      rw [Category.assoc]
      exact hfst
    refine ⟨PullbackCone.IsLimit.mk (mappingPathProd_comm f)
      (fun s => pullback.lift (s.fst ≫ CartesianMonoidalCategory.fst X B) s.snd
        (liftW s)) ?_ ?_ ?_⟩
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, mappingPathProdLift_fst]
        exact pullback.lift_fst _ _ _
      · have hsnd : (s.fst ≫ mappingPathProdMap f) ≫
            CartesianMonoidalCategory.snd B B =
          (s.snd ≫ evalPair) ≫ CartesianMonoidalCategory.snd B B := by
          rw [s.condition]
        rw [Category.assoc, mappingPathProdMap_snd, Category.assoc,
          evalPair_snd] at hsnd
        rw [Category.assoc, mappingPathProdLift_snd, ← Category.assoc,
          pullback.lift_snd]
        exact hsnd.symm
    · intro s
      exact pullback.lift_snd _ _ _
    · intro s m h1 h2
      apply pullback.hom_ext
      · have hfst : (m ≫ mappingPathProdLift f) ≫
            CartesianMonoidalCategory.fst X B =
          s.fst ≫ CartesianMonoidalCategory.fst X B := by
          rw [h1]
        rw [Category.assoc, mappingPathProdLift_fst] at hfst
        rw [hfst]
        exact (pullback.lift_fst _ _ _).symm
      · rw [h2]
        exact (pullback.lift_snd _ _ _).symm

/-- The map `(retract, target)` into the product is a Kan fibration: it
pulls back `evalPair`. -/
private theorem fibration_mappingPathProdLift {X B : SSet.{u}} (f : X ⟶ B)
    [KanComplex B] : Fibration (mappingPathProdLift f) :=
  fibration_of_isPullback (isPullback_mappingPathProd f)

/-- Horn lifting against the second projection: only the `X`-component
needs a lift, which comes from Kan-ness of `X`. (Kept separate so the
`J`-elimination's substitution cannot shadow the outer `X`.) -/
private theorem hasLiftingProperty_horn_snd {X B : SSet.{u}} [KanComplex X]
    {m : ℕ} {k : Fin (m + 2)} :
    HasLiftingProperty (horn (m + 1) k).ι
      (CartesianMonoidalCategory.snd X B) := by
  let _ : Fibration (terminal.from X) := ‹KanComplex X›
  refine ⟨?_⟩
  intro f g sq
  let sqX : CommSq (f ≫ CartesianMonoidalCategory.fst X B) (horn (m + 1) k).ι
      (terminal.from X) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact CartesianMonoidalCategory.lift sqX.lift g
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
      exact sqX.fac_left
    · rw [Category.assoc, CartesianMonoidalCategory.lift_snd]
      exact sq.w.symm
  · exact CartesianMonoidalCategory.lift_snd _ _

/-- The second projection out of a cartesian tensor is a Kan fibration
for Kan domain. -/
instance {X B : SSet.{u}} [KanComplex X] :
    Fibration (CartesianMonoidalCategory.snd X B) := by
  rw [modelCategoryQuillen.fibration_iff]
  intro _ _ _ hh
  simp only [J, MorphismProperty.iSup_iff] at hh
  obtain ⟨m, ⟨k⟩⟩ := hh
  exact hasLiftingProperty_horn_snd

/-- Right-composition stability of the lifting property, dual to
`HasLiftingProperty.of_comp_left`. -/
private theorem hasLiftingProperty_comp_right {A B X Y Z : SSet.{u}} {i : A ⟶ B}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : HasLiftingProperty i f)
    (hg : HasLiftingProperty i g) : HasLiftingProperty i (f ≫ g) := by
  have h1 := HasLiftingProperty.op hf
  have h2 := HasLiftingProperty.op hg
  have h3 : HasLiftingProperty (g.op ≫ f.op) i.op :=
    @HasLiftingProperty.of_comp_left SSet.{u}ᵒᵖ _ _ _ _ _ _ g.op f.op i.op h2 h1
  rw [← CategoryTheory.op_comp] at h3
  exact HasLiftingProperty.unop h3

/-- The mapping-path-space target map is a Kan fibration: it is the map
into the product followed by the second projection. -/
instance {X B : SSet.{u}} (f : X ⟶ B) [KanComplex X] [KanComplex B] :
    Fibration (mappingPathTarget f) := by
  have h : mappingPathTarget f =
      mappingPathProdLift f ≫ CartesianMonoidalCategory.snd X B :=
    (rfl : mappingPathTarget f = pullback.snd f eval₀ ≫ eval₁).trans
      (mappingPathProdLift_snd f).symm
  have hf1 : J.rlp (mappingPathProdLift f) :=
    (modelCategoryQuillen.fibration_iff _).1 (fibration_mappingPathProdLift f)
  have hf2 : J.rlp (CartesianMonoidalCategory.snd X B) :=
    (modelCategoryQuillen.fibration_iff _).1 inferInstance
  have hFib : Fibration (mappingPathProdLift f ≫ CartesianMonoidalCategory.snd X B) := by
    rw [modelCategoryQuillen.fibration_iff]
    intro A B i hi
    exact hasLiftingProperty_comp_right (hf1 i hi) (hf2 i hi)
  rw [h]
  exact hFib

/-! ## Step 3: Kan homotopy pullbacks

A square over a Kan cospan is a Kan homotopy pullback when the comparison
map into the single mapping-path-space replacement of the right leg is a
weak equivalence. Maps of squares over the same cospan induce factorizations
of comparisons, giving 2-of-3 transfer along weak equivalences (and, via
`W.iff_of_homotopy`, along homotopies).
-/

/-- The comparison map from a square's vertex into the mapping-path-space
replacement of the right leg: `P ⟶ X ×_B M_g`. -/
noncomputable def kanHomotopyPullbackComparison {P X Y B : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y} (sq : CommSq u v f g) :
    P ⟶ pullback f (mappingPathTarget g) :=
  pullback.lift u (v ≫ mappingPathSection g) (by
    rw [Category.assoc, mappingPathSection_comp_target]
    exact sq.w)

theorem kanHomotopyPullbackComparison_fst {P X Y B : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y} (sq : CommSq u v f g) :
    kanHomotopyPullbackComparison sq ≫ pullback.fst f _ = u :=
  pullback.lift_fst _ _ _

theorem kanHomotopyPullbackComparison_snd {P X Y B : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y} (sq : CommSq u v f g) :
    kanHomotopyPullbackComparison sq ≫ pullback.snd f _ =
      v ≫ mappingPathSection g :=
  pullback.lift_snd _ _ _

/-- A square over a cospan of Kan complexes is a Kan homotopy pullback if
the comparison into the right-leg mapping-path-space replacement is a
weak equivalence. The right leg is the replaced one. -/
def IsKanHomotopyPullback {P X Y B : SSet.{u}}
    [_kanX : KanComplex X] [_kanY : KanComplex Y] [_kanB : KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y} (sq : CommSq u v f g) :
    Prop :=
  KanComplex.W (kanHomotopyPullbackComparison sq)

/-- Comparisons are natural for maps of squares over the same cospan. -/
private theorem kanHomotopyPullbackComparison_naturality
    {P₁ P₂ X Y B : SSet.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    {u₁ : P₁ ⟶ X} {v₁ : P₁ ⟶ Y} {u₂ : P₂ ⟶ X} {v₂ : P₂ ⟶ Y}
    (sq₁ : CommSq u₁ v₁ f g) (sq₂ : CommSq u₂ v₂ f g)
    (h : P₁ ⟶ P₂) (hu : h ≫ u₂ = u₁) (hv : h ≫ v₂ = v₁) :
    kanHomotopyPullbackComparison sq₁ =
      h ≫ kanHomotopyPullbackComparison sq₂ := by
  apply pullback.hom_ext
  · simp only [kanHomotopyPullbackComparison_fst, Category.assoc, hu]
  · simp only [kanHomotopyPullbackComparison_snd, Category.assoc]
    rw [← Category.assoc, hv]

/-- Two-of-three for Kan homotopy pullbacks along a map of squares: if
the vertex map is a weak equivalence, one square is a homotopy pullback
if and only if the other is. Formal from `W` 2-of-3. -/
theorem homotopyPullback_twoOfThree {P₁ P₂ X Y B : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B}
    {u₁ : P₁ ⟶ X} {v₁ : P₁ ⟶ Y} {u₂ : P₂ ⟶ X} {v₂ : P₂ ⟶ Y}
    (sq₁ : CommSq u₁ v₁ f g) (sq₂ : CommSq u₂ v₂ f g)
    (h : P₁ ⟶ P₂) (hu : h ≫ u₂ = u₁) (hv : h ≫ v₂ = v₁)
    (hh : KanComplex.W h) :
    IsKanHomotopyPullback sq₁ ↔ IsKanHomotopyPullback sq₂ := by
  unfold IsKanHomotopyPullback
  rw [kanHomotopyPullbackComparison_naturality sq₁ sq₂ h hu hv]
  exact KanComplex.W.precomp_iff hh

/-- Homotopy transfer for Kan homotopy pullbacks: the 2-of-3 property
holds along a vertex map homotopic to a weak equivalence. -/
theorem isKanHomotopyPullback_of_homotopy {P₁ P₂ X Y B : SSet.{u}}
    [KanComplex P₁] [KanComplex P₂]
    [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B}
    {u₁ : P₁ ⟶ X} {v₁ : P₁ ⟶ Y} {u₂ : P₂ ⟶ X} {v₂ : P₂ ⟶ Y}
    (sq₁ : CommSq u₁ v₁ f g) (sq₂ : CommSq u₂ v₂ f g)
    {h h' : P₁ ⟶ P₂} (hu : h ≫ u₂ = u₁) (hv : h ≫ v₂ = v₁)
    (H : SSet.Homotopy h h') (hh' : KanComplex.W h') :
    IsKanHomotopyPullback sq₁ ↔ IsKanHomotopyPullback sq₂ := by
  have hh : KanComplex.W h := (KanComplex.W.iff_of_homotopy H).2 hh'
  exact homotopyPullback_twoOfThree sq₁ sq₂ h hu hv hh

/-- The replacement pullback projects to `X` by a weak equivalence when
the replaced leg is one: the target map is then a trivial Kan fibration,
so its pullback is boundary-RLP, hence in `W`. -/
private theorem w_pullback_fst_of_mem {X Y B : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B} (hg : KanComplex.W g) :
    KanComplex.W (pullback.fst f (mappingPathTarget g)) := by
  have hs := KanComplex.W.of_mappingPathSection g
  have hrW : KanComplex.W (mappingPathTarget g) := by
    apply KanComplex.W.of_precomp hs
    rw [mappingPathSection_comp_target g]
    exact hg
  have hr_rlp : I.rlp (mappingPathTarget g) :=
    (KanComplex.I_rlp_iff_W_of_fibration (mappingPathTarget g)).2 hrW
  have hp_rlp : I.rlp (pullback.fst f (mappingPathTarget g)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f _).flip hr_rlp
  exact KanComplex.W.of_rlp_I hp_rlp

/-- Right-leg transfer: in a Kan homotopy pullback square, if the right
cospan leg is a weak equivalence, so is the opposite vertex leg. -/
theorem KanComplex.W.of_isKanHomotopyPullback_right {P X Y B : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y}
    (sq : CommSq u v f g) (hpb : IsKanHomotopyPullback sq)
    (hg : KanComplex.W g) : KanComplex.W u := by
  have hu : u = kanHomotopyPullbackComparison sq ≫ pullback.fst f _ :=
    (kanHomotopyPullbackComparison_fst sq).symm
  rw [hu]
  exact KanComplex.W.comp hpb (w_pullback_fst_of_mem hg)

/-- Boundary RLP implies Kan fibration (boundary RLP is RLP against all
monomorphisms, and horns are monomorphisms). -/
private theorem fibration_of_I_rlp {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : I.rlp p) : Fibration p := by
  rw [modelCategoryQuillen.fibration_iff]
  apply MorphismProperty.antitone_rlp J_le_monomorphisms
  rwa [rlp_monomorphisms]

/-- Strict pullback along a trivial Kan fibration is a Kan homotopy
pullback: the opposite leg is boundary-RLP, and the comparison is a
section-retract 2-of-3 consequence. -/
theorem isKanHomotopyPullback_of_isPullback_of_rlp_I {P X Y B : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y}
    (sq : IsPullback u v f g) (hg : I.rlp g) :
    IsKanHomotopyPullback sq.toCommSq := by
  let _ : Fibration g := fibration_of_I_rlp hg
  let _ : Fibration u := fibration_of_isPullback sq
  let _ : KanComplex P := isFibrant_of_fibration u
  have hu_rlp : I.rlp u := MorphismProperty.of_isPullback sq.flip hg
  have huW : KanComplex.W u := KanComplex.W.of_rlp_I hu_rlp
  have hgW : KanComplex.W g := KanComplex.W.of_rlp_I hg
  have hc_eq : kanHomotopyPullbackComparison sq.toCommSq ≫ pullback.fst f _ = u :=
    kanHomotopyPullbackComparison_fst _
  have hfg : KanComplex.W
      (kanHomotopyPullbackComparison sq.toCommSq ≫ pullback.fst f _) := by
    rw [hc_eq]
    exact huW
  exact KanComplex.W.of_postcomp (w_pullback_fst_of_mem hgW) hfg

end SSet
