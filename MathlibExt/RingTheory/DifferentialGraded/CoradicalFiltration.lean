/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.RingTheory.DifferentialGraded.TwistingAugmentationFactor
public import MathlibExt.RingTheory.DifferentialGraded.TensorPowers
public import MathlibExt.RingTheory.DifferentialGraded.ReducedKernels

/-!
# Predicate-only coradical filtration for coaugmented dg coalgebras

For explicit `η : 𝟙_ ⟶ C` and a candidate `Δbar : C ⟶ C ⊗ C`, `IsRedComul η Δbar`
requires `η` to be a comonoid morphism from the canonical tensor-unit comonoid
(local `ComonObj.instTensorUnit` only), records the honest comultiplication
decomposition with correctly oriented tensor maps and unitors, plus the three
required vanishing equations. Existence is supplied only by the canonical
construction `canonRedComul` / `canonIsRedComul` below, from the explicit
comonoid-morphism laws of `η`. Finite
iterates via `redComulPowFrom Δbar`, stage membership `IsInFilt Δbar` over
those canonical iterates, and exhaustion `IsConilpotent η Δbar` requiring both
the `IsRedComul` witness and finite-stage vanishing are defined below in
this file. See the module nonclaims for the explicit scope boundary.

## Declaration inventory (this leaf)

* `IsRedComul`: `IsComonHom η` from the local tensor-unit comonoid, plus
  decomposition `Δ = Δbar + L η + R η − U η` with exact pinned
  `tensorHom`/unitor paths, plus `η ≫ Δbar = 0` and both counit-leg vanishings.
* `redComulPowFrom`: correctly typed finite iterate `∀ n, C ⟶ tensorPowObj C (n+1)`
  with degree zero the canonical identity-through-degree-one isomorphism and
  successor via the candidate `Δbar` followed by tensoring the previous iterate
  with `𝟙 C`, plus exact zero/successor computation lemmas.
* `IsInFilt`: componentwise stage membership directly over
  `redComulPowFrom Δbar` via the morphism degree component, with the
  deliberate `(n+1)` offset so `F₀ = ker Δbar` up to the degree-one iso.
* `IsConilpotent`: `IsRedComul η Δbar` plus elementwise exhaustion by those
  canonical finite stages, plus the genuinely derivable zero-membership closure
  lemma.
* `redComul`: landing map `coaugCoideal η ⟶ coaugCoideal η ⊗ coaugCoideal η`
  descending `Δbar ≫ π ⊗ π` through the cokernel, plus computation
  `redComul_π`, uniqueness `redComul_unique`, binary leg-transfer
  `redComul_legTransfer` (true comultiplication and candidate agree after
  `π ⊗ π`), and plain coassociativity `redComul_coassoc` on the same
  associator path as `ComonObj.comul_assoc`.
* `redComulPowFrom_split`: generic finite-iterate deconcatenation for an
  arbitrary candidate `Δbar` with explicit binary coassociativity, via the
  committed `tensorPowObj_add` coherence, `tensorHom` functoriality,
  associator naturality, and the triangle coherence; no `ComonObj` assumed.
* `redComulPowFrom_split_redComul`: the same splitting for
  `redComul η Δbar h`, discharging binary coassociativity only from
  `redComul_coassoc`.
* `redComulCandidate_naturality`: forward naturality
  `u ≫ ΔbarD = ΔbarC ≫ tensorHom u u` for a comonoid map `u : C ⟶ D`
  with `ηC ≫ u = ηD`.
* `canonRedComul` / `canonIsRedComul`: the canonical reduced comultiplication
  at a general `η` (full comultiplication minus the two coaugmentation legs
  plus the double-coaugmentation term) and its `IsRedComul` proof from the
  explicit comonoid-morphism laws of `η`.

## Nonclaims

* No `ComonObj` on the coaugmentation cokernel; no `Δbar` existence beyond
  the canonical `canonRedComul` construction from the comonoid-morphism laws
  of `η`; no filtration object, quotient, colimit, or colimit isomorphism
  beyond the cokernel universal property; no counit laws for `redComul`.
* No tensor coalgebra, (co)free objects or universal properties, completeness,
  convolution summability, representability, adjunction, derived or Koszul
  claims, and no C15/C16/KQ/operad result.
* The iterate-splitting theorems claim only the stated deconcatenation with
  exact `m + 1 + n` indexing for an arbitrary candidate; no nilpotence,
  monotonicity, `ComonObj` in the generic statement, cokernel-coalgebra,
  completion, or cofree claim.
* This predicate is not identified with `IsReducedConvNilpotent`: that is a
  cochain-level convolution-nilpotence condition with different carriers
  (`TwistingConilpotentPredicates`), while this is a coalgebra-domain
  reduced-comultiplication condition. Neither direction is claimed here.
* This remains an explicitly documented thin `CochainComplex (ModuleCat R) ℤ`
  specialization; it does not discharge FG7.

## Import justification

`TwistingAugmentationFactor` supplies the
pinned comonoid API (`ComonObj`, `IsComonHom`, `ComonObj.instTensorUnit`;
direct compilation confirms `TensorPowers` alone does not supply these).
`TensorPowers` supplies the left-associated `tensorPowObj` interface used by
`redComulPowFrom`/`IsInFilt` in this file, plus the cochain `tensorHom_zero` /
`zero_tensorHom` lemmas consumed by the `redComul` leg-transfer. `ReducedKernels`
supplies the coaugmentation-cokernel universal-property API (`coaugCoideal`,
`coaugCoidealπ`, `coaugCoideal_desc`, computation, uniqueness, condition); it
imports no C14 leaf, so this edge is acyclic.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [ComonObj C]

/-- Reduced-comultiplication predicate for an explicit coaugmentation `η` and a
candidate `Δbar`: `η` is a comonoid morphism from the canonical tensor-unit
comonoid (local `ComonObj.instTensorUnit` only, no global instance); the actual
comultiplication decomposes as `Δbar` plus the two `η`-legs minus the
double-`η` term, with exact pinned unitor/`tensorHom` paths; moreover `η`
kills `Δbar` and both counit legs kill `Δbar`. Existence of `Δbar` is not
claimed. -/
def IsRedComul (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) : Prop :=
  (letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
    ; IsComonHom η) ∧
    ComonObj.comul (X := C) =
      Δbar +
        ((HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom η (𝟙 C)) +
        ((HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom (𝟙 C) η) -
        (ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η η) ∧
    η ≫ Δbar = 0 ∧
    Δbar ≫ HomologicalComplex.tensorHom (ComonObj.counit (X := C)) (𝟙 C) = 0 ∧
    Δbar ≫ HomologicalComplex.tensorHom (𝟙 C) (ComonObj.counit (X := C)) = 0

/-- Finite iterate of a candidate reduced comultiplication: `0` is the canonical
identity-through-degree-one isomorphism (not an ill-typed literal identity);
successor is the candidate `Δbar` followed by tensoring the previous iterate
with `𝟙 C`. Uses only the committed `TensorPowers` interface; no coherence is
reproved here. -/
noncomputable def redComulPowFrom
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) :
    ∀ n, C ⟶ tensorPowObj C (n + 1)
  | 0 => (HomologicalComplex.leftUnitor C).symm.hom
  | n + 1 => Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar n) (𝟙 C)

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [ComonObj C] in
/-- Endpoint computation for `redComulPowFrom`: degree `0` is the canonical
identity-through-degree-one isomorphism onto `tensorPowObj C 1`; the index
`0` means `0 + 1`. -/
@[simp]
theorem redComulPowFrom_zero
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) :
    redComulPowFrom Δbar 0 = (HomologicalComplex.leftUnitor C).symm.hom :=
  rfl

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [ComonObj C] in
/-- Recursive computation for `redComulPowFrom`: degree `n + 1` applies the
candidate `Δbar` then tensors the degree-`n` iterate with `𝟙 C` on the right;
the target index grows as `(n + 1) + 1`. -/
@[simp]
theorem redComulPowFrom_succ
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) (n : ℕ) :
    redComulPowFrom Δbar (n + 1) =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar n) (𝟙 C) :=
  rfl

/-- Componentwise stage membership: `x` lies in stage `n` when the degree
component of the `(n+1)`-st canonical iterate `redComulPowFrom Δbar`
vanishes on it. The `(n+1)` offset is deliberate: `redComulPowFrom Δbar 0`
is the degree-one iso, so `F₀` is the kernel of `Δbar` up to that iso. Never
spelled as ill-typed morphism-applied-to-element. -/
def IsInFilt (Δbar : C ⟶ HomologicalComplex.tensorObj C C) (n : ℕ) (i : ℤ)
    (x : C.X i) : Prop :=
  ((redComulPowFrom Δbar (n + 1)).f i) x = 0

/-- Elementwise conilpotence as exhaustion by the finite stages of the actual
candidate `Δbar`: `IsRedComul η Δbar` holds and every degree component of
every element vanishes at some finite canonical stage. The `IsRedComul`
conjunct ties `Δbar` to the true coalgebra comultiplication, so the zero
candidate and arbitrary families no longer trivialize the notion. No
completeness, limits, or colimit isomorphism is claimed. -/
def IsConilpotent (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) : Prop :=
  IsRedComul η Δbar ∧ ∀ (i : ℤ) (x : C.X i), ∃ n, IsInFilt Δbar n i x

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [ComonObj C] in
/-- Zero lies in every stage, via the pinned linear-map `map_zero`. This is the
only closure fact claimed here; monotonicity, transport, and any identification
with `IsReducedConvNilpotent` are explicitly not claimed. -/
theorem IsInFilt_zero (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (n : ℕ) (i : ℤ) :
    IsInFilt Δbar n i 0 :=
  map_zero _

/-- Reduced comultiplication landing on the coaugmentation coideal: descends
`Δbar ≫ π ⊗ π` through the cokernel projection. The obligation is
`η ≫ Δbar = 0` transported past the tensorHom legs. -/
noncomputable def redComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    coaugCoideal η ⟶
      HomologicalComplex.tensorObj (coaugCoideal η) (coaugCoideal η) := by
  refine coaugCoideal_desc η
    (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
      (coaugCoidealπ η)) ?_
  rw [← Category.assoc, h.2.2.1, zero_comp]

/-- Computation: projecting then applying `redComul` equals `Δbar` followed by
`π ⊗ π`. -/
theorem redComul_π
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    coaugCoidealπ η ≫ redComul η Δbar h =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η) := by
  unfold redComul
  exact coaugCoideal_π_desc η _ _

/-- Uniqueness: any map out of the coideal agreeing with `Δbar ≫ π ⊗ π`
after the projection is `redComul`. -/
theorem redComul_unique
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar)
    (g : coaugCoideal η ⟶ HomologicalComplex.tensorObj (coaugCoideal η)
      (coaugCoideal η))
    (hg : coaugCoidealπ η ≫ g = Δbar ≫ HomologicalComplex.tensorHom
      (coaugCoidealπ η) (coaugCoidealπ η)) :
    g = redComul η Δbar h := by
  unfold redComul
  exact coaugCoideal_desc_unique η _ _ g hg

/-- Binary leg-transfer: the true comultiplication and the candidate agree
after `π ⊗ π`. The `η`-legs die by `coaugCoideal_condition` plus the cochain
`tensorHom_zero` / `zero_tensorHom` lemmas. -/
theorem redComul_legTransfer
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    ComonObj.comul (X := C) ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η) =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η) := by
  have hdecomp := h.2.1
  have hL : ((HomologicalComplex.leftUnitor C).inv ≫
      HomologicalComplex.tensorHom η (𝟙 C)) ≫
      HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η) = 0 := by
    rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
      coaugCoideal_condition, zero_tensorHom, comp_zero]
  have hR : ((HomologicalComplex.rightUnitor C).inv ≫
      HomologicalComplex.tensorHom (𝟙 C) η) ≫
      HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η) = 0 := by
    rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
      coaugCoideal_condition, tensorHom_zero, comp_zero]
  have hU : (ComonObj.counit (X := C) ≫
      (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom η η) ≫
      HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η) = 0 := by
    rw [Category.assoc, Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
      coaugCoideal_condition, zero_tensorHom, comp_zero,
      comp_zero]
  rw [hdecomp, Preadditive.sub_comp, Preadditive.add_comp,
    Preadditive.add_comp, hL, hR, hU, add_zero, add_zero, sub_zero]

/-- Plain coassociativity of `redComul`: same associator path as
`ComonObj.comul_assoc`, with `redComul` in place of `comul`. No counit laws
are claimed. The proof pushes the projection through both sides, replays the
base coassociativity under the triple projection, then replaces the leading
`Δ` by `Δbar` via the decomposition (the `η`-legs vanish on both
triple-tensor targets). -/
theorem redComul_coassoc
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    redComul η Δbar h ≫
        coaugCoideal η ◁ redComul η Δbar h =
      redComul η Δbar h ≫
        (redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom := by
  have hπ := redComul_π η Δbar h
  have hleg := redComul_legTransfer η Δbar h
  have hdecomp := h.2.1
  have hη : η ≫ (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
      (coaugCoidealπ η)) = 0 := by
    rw [← Category.assoc, h.2.2.1, zero_comp]
  have hLHS : coaugCoidealπ η ≫ (redComul η Δbar h ≫
      coaugCoideal η ◁ redComul η Δbar h) =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) := by
    erw [← Category.assoc, hπ, Category.assoc,
      MonoidalCategory.tensorHom_comp_whiskerLeft, hπ]
    rfl
  have hRHS : coaugCoidealπ η ≫ (redComul η Δbar h ≫
      (redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom) =
      Δbar ≫ ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    erw [← Category.assoc (coaugCoidealπ η) (redComul η Δbar h)
      ((redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom), hπ,
      ← Category.assoc
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η))
        (redComul η Δbar h ▷ coaugCoideal η)
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
      Category.assoc Δbar
        (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))
        (redComul η Δbar h ▷ coaugCoideal η),
      MonoidalCategory.tensorHom_comp_whiskerRight, hπ, Category.assoc]
  have hbase := ComonObj.comul_assoc C
  have hpost : (ComonObj.comul (X := C) ≫
      C ◁ ComonObj.comul (X := C)) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η)) =
      (ComonObj.comul (X := C) ≫ ((ComonObj.comul (X := C) ▷ C) ≫
        (α_ C C C).hom)) ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) := by
    rw [hbase]
  erw [Category.assoc (ComonObj.comul (X := C))
    (C ◁ ComonObj.comul (X := C))
    (HomologicalComplex.tensorHom (coaugCoidealπ η)
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))),
    MonoidalCategory.whiskerLeft_comp_tensorHom] at hpost
  have hnat : (HomologicalComplex.tensorHom
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))
        (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom =
      (α_ C C C).hom ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) :=
    MonoidalCategory.associator_naturality (coaugCoidealπ η)
      (coaugCoidealπ η) (coaugCoidealπ η)
  erw [Category.assoc (ComonObj.comul (X := C))
    ((ComonObj.comul (X := C) ▷ C) ≫ (α_ C C C).hom)
    (HomologicalComplex.tensorHom (coaugCoidealπ η)
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))),
    Category.assoc (ComonObj.comul (X := C) ▷ C) (α_ C C C).hom
    (HomologicalComplex.tensorHom (coaugCoidealπ η)
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))),
    ← hnat,
    ← Category.assoc (ComonObj.comul (X := C) ▷ C)
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))
        (coaugCoidealπ η))
      (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
    MonoidalCategory.whiskerRight_comp_tensorHom] at hpost
  rw [hleg] at hpost
  have hSL : ComonObj.comul (X := C) ≫ HomologicalComplex.tensorHom
      (coaugCoidealπ η) (Δbar ≫ HomologicalComplex.tensorHom
        (coaugCoidealπ η) (coaugCoidealπ η)) =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) := by
    have V1 : ((HomologicalComplex.leftUnitor C).inv ≫
        HomologicalComplex.tensorHom η (𝟙 C)) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) = 0 := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        coaugCoideal_condition, zero_tensorHom, comp_zero]
    have V2 : ((HomologicalComplex.rightUnitor C).inv ≫
        HomologicalComplex.tensorHom (𝟙 C) η) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) = 0 := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom, hη,
        tensorHom_zero, comp_zero]
    have V3 : (ComonObj.counit (X := C) ≫
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η η) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) = 0 := by
      rw [Category.assoc, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom, coaugCoideal_condition,
        hη, zero_tensorHom, comp_zero, comp_zero]
    rw [hdecomp, Preadditive.sub_comp, Preadditive.add_comp,
      Preadditive.add_comp, V1, V2, V3, add_zero, add_zero, sub_zero]
  have hSR : ComonObj.comul (X := C) ≫
      ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) =
      Δbar ≫ ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    have V4 : ((HomologicalComplex.leftUnitor C).inv ≫
        HomologicalComplex.tensorHom η (𝟙 C)) ≫
        ((HomologicalComplex.tensorHom
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
          (α_ (coaugCoideal η) (coaugCoideal η)
            (coaugCoideal η)).hom) = 0 := by
      rw [Category.assoc,
        ← Category.assoc (HomologicalComplex.tensorHom η (𝟙 C))
          (HomologicalComplex.tensorHom
            (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
              (coaugCoidealπ η)) (coaugCoidealπ η))
          (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
        HomologicalComplex.tensorHom_comp_tensorHom, hη, zero_tensorHom,
        zero_comp, comp_zero]
    have V5 : ((HomologicalComplex.rightUnitor C).inv ≫
        HomologicalComplex.tensorHom (𝟙 C) η) ≫
        ((HomologicalComplex.tensorHom
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
          (α_ (coaugCoideal η) (coaugCoideal η)
            (coaugCoideal η)).hom) = 0 := by
      rw [Category.assoc,
        ← Category.assoc (HomologicalComplex.tensorHom (𝟙 C) η)
          (HomologicalComplex.tensorHom
            (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
              (coaugCoidealπ η)) (coaugCoidealπ η))
          (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
        HomologicalComplex.tensorHom_comp_tensorHom, coaugCoideal_condition,
        tensorHom_zero, zero_comp, comp_zero]
    have V6 : (ComonObj.counit (X := C) ≫
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η η) ≫
        ((HomologicalComplex.tensorHom
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
          (α_ (coaugCoideal η) (coaugCoideal η)
            (coaugCoideal η)).hom) = 0 := by
      rw [Category.assoc, Category.assoc,
        ← Category.assoc (HomologicalComplex.tensorHom η η)
          (HomologicalComplex.tensorHom
            (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
              (coaugCoidealπ η)) (coaugCoidealπ η))
          (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
        HomologicalComplex.tensorHom_comp_tensorHom, hη,
        coaugCoideal_condition, zero_tensorHom, zero_comp,
        comp_zero, comp_zero]
    rw [hdecomp, Preadditive.sub_comp, Preadditive.add_comp,
      Preadditive.add_comp, V4, V5, V6, add_zero, add_zero, sub_zero]
  have hdone : Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
      (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η)) =
      Δbar ≫ ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    rw [← hSL, ← hSR]
    exact hpost
  have key : coaugCoidealπ η ≫ (redComul η Δbar h ≫
      coaugCoideal η ◁ redComul η Δbar h) =
      coaugCoidealπ η ≫ (redComul η Δbar h ≫
        (redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    rw [hLHS, hRHS]
    exact hdone
  exact Cofork.IsColimit.hom_ext (cokernelIsCokernel η) key

private theorem redComulUnitTensorStep
    {D : Type*} [Category D] [MonoidalCategory D] {X P : D}
    (δ : X ⟶ X ⊗ X) (f : X ⟶ P) :
    (δ ≫ (f ⊗ₘ 𝟙 X)) ≫
        (((ρ_ P).inv ⊗ₘ 𝟙 X) ≫ (α_ P (𝟙_ D) X).hom) =
      δ ≫ (f ⊗ₘ (λ_ X).inv) := by
  have hTri : ((ρ_ P).inv ⊗ₘ 𝟙 X) ≫ (α_ P (𝟙_ D) X).hom =
      𝟙 P ⊗ₘ (λ_ X).inv := by
    simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      MonoidalCategory.triangle_assoc_comp_right_inv P X
  rw [hTri, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp]

private theorem redComulCoassocTensorStep
    {D : Type*} [Category D] [MonoidalCategory D] {X P Q A : D}
    (δ : X ⟶ X ⊗ X)
    (hcoassoc : δ ≫ (𝟙 X ⊗ₘ δ) =
      δ ≫ (δ ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom)
    (f : X ⟶ P) (g : X ⟶ Q) (r : X ⟶ A) (a : A ⟶ P ⊗ Q)
    (h : r ≫ a = δ ≫ (f ⊗ₘ g)) :
    (δ ≫ (r ⊗ₘ 𝟙 X)) ≫ ((a ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom) =
      δ ≫ (f ⊗ₘ (δ ≫ (g ⊗ₘ 𝟙 X))) := by
  have hLeft : (r ⊗ₘ 𝟙 X) ≫ (a ⊗ₘ 𝟙 X) = (r ≫ a) ⊗ₘ 𝟙 X := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have hSplit : (δ ≫ (f ⊗ₘ g)) ⊗ₘ 𝟙 X =
      (δ ⊗ₘ 𝟙 X) ≫ ((f ⊗ₘ g) ⊗ₘ 𝟙 X) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have hAssoc : ((f ⊗ₘ g) ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom =
      (α_ X X X).hom ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X)) :=
    MonoidalCategory.associator_naturality f g (𝟙 X)
  calc
    _ = δ ≫ (((r ⊗ₘ 𝟙 X) ≫ (a ⊗ₘ 𝟙 X)) ≫ (α_ P Q X).hom) := by
      simp only [Category.assoc]
    _ = δ ≫ (((r ≫ a) ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom) := by rw [hLeft]
    _ = δ ≫ (((δ ≫ (f ⊗ₘ g)) ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom) := by rw [h]
    _ = δ ≫ (δ ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X)) := by
      rw [hSplit]
      simp only [Category.assoc]
      rw [hAssoc]
    _ = δ ≫ (𝟙 X ⊗ₘ δ) ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X)) := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X))) hcoassoc.symm
    _ = _ := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

omit [ComonObj C] in
/-- Generic finite-iterate splitting for an arbitrary reduced-comultiplication
candidate: with explicit binary coassociativity, the `(m+1+n)`-th iterate
deconcatenates through the finite-add coherence into the tensor of the `m`-th
and `n`-th iterates. No `ComonObj` is assumed. -/
theorem redComulPowFrom_split
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (hcoassoc : Δbar ≫ HomologicalComplex.tensorHom (𝟙 C) Δbar =
      Δbar ≫ HomologicalComplex.tensorHom Δbar (𝟙 C) ≫ (α_ C C C).hom)
    (m n : ℕ) :
    redComulPowFrom Δbar (m + 1 + n) ≫
      (tensorPowObj_add C (m + 1) (n + 1)).hom =
    Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
      (redComulPowFrom Δbar n) := by
  induction n with
  | zero =>
    have hR0 : redComulPowFrom Δbar 0 =
        (HomologicalComplex.leftUnitor C).symm.hom := rfl
    have hRsucc : redComulPowFrom Δbar (m + 1) =
        Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
          (𝟙 C) := rfl
    have hE0 : (eqToIso (congrArg (tensorPowObj C)
        (Nat.add_zero (m + 1)))).hom = 𝟙 _ := rfl
    have hAdd0 : (tensorPowObj_add C (m + 1) 0).hom =
        (HomologicalComplex.rightUnitor (tensorPowObj C (m + 1))).symm.hom := by
      rw [tensorPowObj_add_zero_right, hE0,
        CategoryTheory.Category.id_comp]
    have hE1 : (eqToIso (congrArg (tensorPowObj C)
        (Nat.add_succ (m + 1) 0))).hom = 𝟙 _ := rfl
    have hIso0 : (tensorIsoRight (tensorPowObj_add C (m + 1) 0)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add C (m + 1) 0).hom (𝟙 C) := rfl
    have hAdd1 : (tensorPowObj_add C (m + 1) 1).hom =
        HomologicalComplex.tensorHom
          (HomologicalComplex.rightUnitor
            (tensorPowObj C (m + 1))).symm.hom (𝟙 C) ≫
          (HomologicalComplex.associator (tensorPowObj C (m + 1))
            (tensorPowObj C 0) C).hom := by
      have hDef : (tensorPowObj_add C (m + 1) 1).hom =
          (eqToIso (congrArg (tensorPowObj C)
            (Nat.add_succ (m + 1) 0))).hom ≫
            (tensorIsoRight (tensorPowObj_add C (m + 1) 0)).hom ≫
            (HomologicalComplex.associator (tensorPowObj C (m + 1))
              (tensorPowObj C 0) C).hom := rfl
      rw [hDef, hE1, CategoryTheory.Category.id_comp, hIso0, hAdd0]
      rfl
    change redComulPowFrom Δbar (m + 1) ≫
        (tensorPowObj_add C (m + 1) 1).hom =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
        (redComulPowFrom Δbar 0)
    simp only [hRsucc, hR0, hAdd1]
    change (Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
          (𝟙 C)) ≫
        (HomologicalComplex.tensorHom (HomologicalComplex.rightUnitor
          (tensorPowObj C (m + 1))).symm.hom (𝟙 C) ≫
          (HomologicalComplex.associator (tensorPowObj C (m + 1))
            (HomologicalComplex.tensorUnit (ModuleCat R)
              (ComplexShape.up ℤ)) C).hom) =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
        (HomologicalComplex.leftUnitor C).symm.hom
    exact redComulUnitTensorStep
      (D := CochainComplex (ModuleCat R) ℤ) Δbar (redComulPowFrom Δbar m)
  | succ k ih =>
    have hRsucc : redComulPowFrom Δbar (m + 1 + (k + 1)) =
        Δbar ≫ HomologicalComplex.tensorHom
          (redComulPowFrom Δbar (m + 1 + k)) (𝟙 C) := rfl
    have hE : (eqToIso (congrArg (tensorPowObj C)
        (Nat.add_succ (m + 1) (k + 1)))).hom = 𝟙 _ := rfl
    have hAdd : (tensorPowObj_add C (m + 1) (k + 1 + 1)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add C (m + 1) (k + 1)).hom (𝟙 C) ≫
          (HomologicalComplex.associator _ _ _).hom := by
      have hDef : (tensorPowObj_add C (m + 1) (k + 1 + 1)).hom =
          (eqToIso (congrArg (tensorPowObj C)
            (Nat.add_succ (m + 1) (k + 1)))).hom ≫
            (tensorIsoRight
              (tensorPowObj_add C (m + 1) (k + 1))).hom ≫
            (HomologicalComplex.associator _ _ _).hom := rfl
      rw [hDef, hE, CategoryTheory.Category.id_comp]
      rfl
    have hRstep : redComulPowFrom Δbar (k + 1) =
        Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar k)
          (𝟙 C) := rfl
    simp only [hRsucc, hAdd, hRstep]
    change (Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar (m + 1 + k))
          (𝟙 C)) ≫
        (HomologicalComplex.tensorHom (tensorPowObj_add C (m + 1) (k + 1)).hom
          (𝟙 C) ≫
          (HomologicalComplex.associator (tensorPowObj C (m + 1))
            (tensorPowObj C (k + 1)) C).hom) =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
        (Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar k) (𝟙 C))
    exact redComulCoassocTensorStep
      (D := CochainComplex (ModuleCat R) ℤ) Δbar hcoassoc
      (redComulPowFrom Δbar m) (redComulPowFrom Δbar k)
      (redComulPowFrom Δbar (m + 1 + k))
      (tensorPowObj_add C (m + 1) (k + 1)).hom ih

/-- Splitting for the descended `redComul`: binary coassociativity comes only
from `redComul_coassoc`, with no extra hypothesis beyond `IsRedComul`. -/
theorem redComulPowFrom_split_redComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) (m n : ℕ) :
    redComulPowFrom (redComul η Δbar h) (m + 1 + n) ≫
      (tensorPowObj_add (coaugCoideal η) (m + 1) (n + 1)).hom =
    (redComul η Δbar h) ≫ HomologicalComplex.tensorHom
      (redComulPowFrom (redComul η Δbar h) m)
      (redComulPowFrom (redComul η Δbar h) n) := by
  have hbase := redComul_coassoc η Δbar h
  have hcoassoc : (redComul η Δbar h) ≫
        HomologicalComplex.tensorHom (𝟙 (coaugCoideal η))
          (redComul η Δbar h) =
      (redComul η Δbar h) ≫
        HomologicalComplex.tensorHom (redComul η Δbar h)
          (𝟙 (coaugCoideal η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom := by
    have hL : HomologicalComplex.tensorHom (𝟙 (coaugCoideal η))
          (redComul η Δbar h) =
        (coaugCoideal η ◁ redComul η Δbar h) := by
      change MonoidalCategory.tensorHom (𝟙 (coaugCoideal η))
        (redComul η Δbar h) = _
      rw [MonoidalCategory.id_tensorHom]
    have hR : HomologicalComplex.tensorHom (redComul η Δbar h)
          (𝟙 (coaugCoideal η)) =
        (redComul η Δbar h ▷ coaugCoideal η) := by
      change MonoidalCategory.tensorHom (redComul η Δbar h)
        (𝟙 (coaugCoideal η)) = _
      rw [MonoidalCategory.tensorHom_id]
    rw [hL, hR]
    exact hbase
  exact redComulPowFrom_split _ hcoassoc m n

/-- reduced-comultiplication candidate naturality for a comonoid morphism preserving the
coaugmentation: expanding both full comultiplications by the two `IsRedComul`
decompositions, the two coaugmentation legs and the double leg agree by unitor
naturality, interchange, `hη`, and `hom_counit`, and additive cancellation
leaves the reduced parts equal. This builds no category, functor, adjunction,
or total object, and removes no stored naturality hypothesis elsewhere. -/
theorem redComulCandidate_naturality
    {D : CochainComplex (ModuleCat R) ℤ} [ComonObj D]
    {ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D}
    {ΔbarC : C ⟶ HomologicalComplex.tensorObj C C}
    {ΔbarD : D ⟶ HomologicalComplex.tensorObj D D}
    (hRedC : IsRedComul ηC ΔbarC) (hRedD : IsRedComul ηD ΔbarD)
    (u : C ⟶ D) [IsComonHom u]
    (hη : ηC ≫ u = ηD) :
    u ≫ ΔbarD = ΔbarC ≫ HomologicalComplex.tensorHom u u := by
  have hC := hRedC.2.1
  have hD := hRedD.2.1
  have hcomul : u ≫ ComonObj.comul (X := D) =
      ComonObj.comul (X := C) ≫ HomologicalComplex.tensorHom u u :=
    IsComonHom.hom_comul u
  have hcounit : u ≫ ComonObj.counit (X := D) = ComonObj.counit (X := C) :=
    IsComonHom.hom_counit u
  have hL : u ≫ ((HomologicalComplex.leftUnitor D).inv ≫
      HomologicalComplex.tensorHom ηD (𝟙 D)) =
      ((HomologicalComplex.leftUnitor C).inv ≫
        HomologicalComplex.tensorHom ηC (𝟙 C)) ≫
        HomologicalComplex.tensorHom u u := by
    have hbridgeC : (HomologicalComplex.leftUnitor C).inv = (λ_ C).inv := rfl
    have hbridgeD : (HomologicalComplex.leftUnitor D).inv = (λ_ D).inv := rfl
    have hnat := MonoidalCategory.leftUnitor_inv_naturality u
    have e : (𝟙_ (CochainComplex (ModuleCat R) ℤ) ◁ u) =
        HomologicalComplex.tensorHom (𝟙 _) u := rfl
    have hLHS : u ≫ ((HomologicalComplex.leftUnitor D).inv ≫
          HomologicalComplex.tensorHom ηD (𝟙 D)) =
        (HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom ηD u := by
      rw [hbridgeD, ← Category.assoc, hnat, e, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id, hbridgeC]
    have hRHS : ((HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom ηC (𝟙 C)) ≫
          HomologicalComplex.tensorHom u u =
        (HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom ηD u := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        hη, Category.id_comp]
    exact hLHS.trans hRHS.symm
  have hR : u ≫ ((HomologicalComplex.rightUnitor D).inv ≫
      HomologicalComplex.tensorHom (𝟙 D) ηD) =
      ((HomologicalComplex.rightUnitor C).inv ≫
        HomologicalComplex.tensorHom (𝟙 C) ηC) ≫
        HomologicalComplex.tensorHom u u := by
    have hbridgeC : (HomologicalComplex.rightUnitor C).inv = (ρ_ C).inv := rfl
    have hbridgeD : (HomologicalComplex.rightUnitor D).inv = (ρ_ D).inv := rfl
    have hnat := MonoidalCategory.rightUnitor_inv_naturality u
    have e : (u ▷ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        HomologicalComplex.tensorHom u (𝟙 _) := rfl
    have hLHS : u ≫ ((HomologicalComplex.rightUnitor D).inv ≫
          HomologicalComplex.tensorHom (𝟙 D) ηD) =
        (HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom u ηD := by
      rw [hbridgeD, ← Category.assoc, hnat, e, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp, hbridgeC]
    have hRHS : ((HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom (𝟙 C) ηC) ≫
          HomologicalComplex.tensorHom u u =
        (HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom u ηD := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        hη, Category.id_comp]
    exact hLHS.trans hRHS.symm
  have hU : u ≫ (ComonObj.counit (X := D) ≫
      (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom ηD ηD) =
      (ComonObj.counit (X := C) ≫
        (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom ηC ηC) ≫
        HomologicalComplex.tensorHom u u := by
    have e : HomologicalComplex.tensorHom ηC ηC ≫
        HomologicalComplex.tensorHom u u =
        HomologicalComplex.tensorHom ηD ηD := by
      rw [HomologicalComplex.tensorHom_comp_tensorHom, hη]
    have hLHS : u ≫ (ComonObj.counit (X := D) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηD ηD) =
        ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηD ηD := by
      rw [← Category.assoc, hcounit]
    have hRHS : (ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηC ηC) ≫
          HomologicalComplex.tensorHom u u =
        ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηD ηD := by
      simp only [Category.assoc]
      rw [e]
    exact hLHS.trans hRHS.symm
  rw [hD, hC] at hcomul
  simp only [Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp, hL, hR, hU] at hcomul
  simp only [sub_eq_add_neg] at hcomul
  exact add_right_cancel (add_right_cancel (add_right_cancel hcomul))

/-- Coideal reduced-comultiplication compatibility for a comonoid map,
general over the backward map and its coideal descent: from the
projection compatibility `hπ` and the reduced-comultiplication
compatibility `hΔ`, by the cokernel universal property and the
`IsRedComul` decomposition. Shared by the cofree-tensor-coalgebra
reduced-power induction and the Cobar insertion-naturality lane (which
instantiates it with the roles swapped). -/
theorem coideal_redComul_naturality
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (hRed : IsRedComul η Δbar)
    {D : CochainComplex (ModuleCat R) ℤ}
    [ComonObj D]
    (ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D)
    (ΔbarD : D ⟶ HomologicalComplex.tensorObj D D)
    (hRedD : IsRedComul ηD ΔbarD)
    (u : D ⟶ C)
    (uC : coaugCoideal ηD ⟶ coaugCoideal η)
    (hπ : coaugCoidealπ ηD ≫ uC = u ≫ coaugCoidealπ η)
    (hΔ : u ≫ Δbar =
      ΔbarD ≫ HomologicalComplex.tensorHom u u) :
    uC ≫ redComul η Δbar hRed =
      redComul ηD ΔbarD hRedD ≫
        HomologicalComplex.tensorHom uC uC := by
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel ηD)
  calc coaugCoidealπ ηD ≫
          (uC ≫ redComul η Δbar hRed) =
        u ≫ (coaugCoidealπ η ≫ redComul η Δbar hRed) := by
        rw [← Category.assoc, hπ, Category.assoc]
    _ = u ≫ (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) := by
        rw [redComul_π]
    _ = ΔbarD ≫ HomologicalComplex.tensorHom (u ≫ coaugCoidealπ η)
          (u ≫ coaugCoidealπ η) := by
        rw [← Category.assoc, hΔ, Category.assoc,
          HomologicalComplex.tensorHom_comp_tensorHom]
    _ = ΔbarD ≫ HomologicalComplex.tensorHom (coaugCoidealπ ηD ≫ uC)
          (coaugCoidealπ ηD ≫ uC) := by
        rw [← hπ]
    _ = (ΔbarD ≫ HomologicalComplex.tensorHom (coaugCoidealπ ηD)
          (coaugCoidealπ ηD)) ≫
          HomologicalComplex.tensorHom uC uC := by
        rw [← HomologicalComplex.tensorHom_comp_tensorHom]
        simp only [Category.assoc]
    _ = coaugCoidealπ ηD ≫ (redComul ηD ΔbarD hRedD ≫
          HomologicalComplex.tensorHom uC uC) := by
        rw [← redComul_π, Category.assoc]

/-- Canonical reduced comultiplication at an explicit coaugmentation `η`: the full
comultiplication minus the two coaugmentation legs plus the
double-coaugmentation term. Same formula as the Bar-total
`barShiftedTotalRedComul`, at the comonoid structure maps of `C`. -/
noncomputable def canonRedComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    C ⟶ HomologicalComplex.tensorObj C C :=
  ComonObj.comul (X := C) -
    ((HomologicalComplex.leftUnitor C).inv ≫
      HomologicalComplex.tensorHom η (𝟙 C)) -
    ((HomologicalComplex.rightUnitor C).inv ≫
      HomologicalComplex.tensorHom (𝟙 C) η) +
    (ComonObj.counit (X := C) ≫
      (HomologicalComplex.leftUnitor (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
      HomologicalComplex.tensorHom η η)

set_option linter.style.haveILetI false in
/-- The canonical reduced comultiplication satisfies `IsRedComul`. The
comonoid-morphism laws of `η` are explicit hypotheses (stated in
`HomologicalComplex` spelling) since `IsComonHom η` needs a `ComonObj 𝟙_`
instance the caller may not have in scope. -/
theorem canonIsRedComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (hcounit : η ≫ (ComonObj.counit (X := C)) = 𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
    (hcomul : η ≫ ComonObj.comul (X := C) =
      (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom η η) :
    IsRedComul η (canonRedComul η) := by
  letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
  have hHom : IsComonHom η := { hom_counit := hcounit, hom_comul := hcomul }
  have hUnitors : (HomologicalComplex.leftUnitor
        (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv =
      (HomologicalComplex.rightUnitor
        (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv := by
    have hLU : HomologicalComplex.leftUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        MonoidalCategory.leftUnitor _ := rfl
    have hRU : HomologicalComplex.rightUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        MonoidalCategory.rightUnitor _ := rfl
    rw [hLU, hRU]
    have hIso : MonoidalCategory.leftUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        MonoidalCategory.rightUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) :=
      Iso.ext (MonoidalCategory.unitors_equal
        (C := CochainComplex (ModuleCat R) ℤ))
    rw [hIso]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hHom
  · have hdecomp : ComonObj.comul (X := C) =
        canonRedComul η +
          ((HomologicalComplex.leftUnitor C).inv ≫
            HomologicalComplex.tensorHom η (𝟙 C)) +
          ((HomologicalComplex.rightUnitor C).inv ≫
            HomologicalComplex.tensorHom (𝟙 C) η) -
          (ComonObj.counit (X := C) ≫
            (HomologicalComplex.leftUnitor (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η η) := by
      unfold canonRedComul
      abel
    exact hdecomp
  · have hηL : η ≫
          ((HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 C)) =
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η
            η := by
      rw [← Category.assoc]
      have hnat : η ≫
            (HomologicalComplex.leftUnitor _).inv =
          (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
              η :=
        MonoidalCategory.leftUnitor_inv_naturality _
      rw [hnat, Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    have hηR : η ≫
          ((HomologicalComplex.rightUnitor C).inv ≫
            HomologicalComplex.tensorHom (𝟙 C)
              η) =
        (HomologicalComplex.rightUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
          HomologicalComplex.tensorHom η
            η := by
      rw [← Category.assoc]
      have hnat : η ≫
            (HomologicalComplex.rightUnitor C).inv =
          (HomologicalComplex.rightUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) :=
        MonoidalCategory.rightUnitor_inv_naturality η
      rw [hnat, Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    have hηU : η ≫
          (ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
          HomologicalComplex.tensorHom η
            η) =
        (HomologicalComplex.leftUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
          HomologicalComplex.tensorHom η
            η := by
      rw [← Category.assoc, ← Category.assoc, hcounit, Category.id_comp]
    have hEq : (HomologicalComplex.leftUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η
              η =
          (HomologicalComplex.rightUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η
              η := by
      rw [hUnitors]
    change η ≫ canonRedComul η = 0
    unfold canonRedComul
    rw [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.comp_sub,
      hcomul, hηL, hηR, hηU, ← hEq]
    abel
  · have hΔε : ComonObj.comul (X := C) ≫
          HomologicalComplex.tensorHom (ComonObj.counit (X := C))
            (𝟙 C) =
        (HomologicalComplex.leftUnitor _).inv :=
      ComonObj.counit_comul _
    have hLε : ((HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 C)) ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 C) =
        (HomologicalComplex.leftUnitor _).inv := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        hcounit, Category.id_comp, HomologicalComplex.tensorHom_id_id]
      rfl
    have hRε : ((HomologicalComplex.rightUnitor _).inv ≫
            HomologicalComplex.tensorHom (𝟙 C)
              η) ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 C) =
        (HomologicalComplex.rightUnitor _).inv ≫
          HomologicalComplex.tensorHom (ComonObj.counit (X := C))
            η := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    have hUε : (ComonObj.counit (X := C) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              η) ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 C) =
        (ComonObj.counit (X := C)) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom
            (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
            η := by
      rw [Category.assoc, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id, hcounit]
    have hRU : (HomologicalComplex.rightUnitor _).inv ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              η =
          (ComonObj.counit (X := C)) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
              η := by
      have hfactor : HomologicalComplex.tensorHom
              (ComonObj.counit (X := C))
              η =
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) ≫
              HomologicalComplex.tensorHom (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
                η := by
        rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id,
          Category.id_comp]
      have hnatR : (HomologicalComplex.rightUnitor _).inv ≫
              HomologicalComplex.tensorHom (ComonObj.counit (X := C))
                (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) =
            (ComonObj.counit (X := C)) ≫
              (HomologicalComplex.rightUnitor _).inv :=
        (MonoidalCategory.rightUnitor_inv_naturality _).symm
      rw [hfactor, ← Category.assoc, hnatR, Category.assoc, hUnitors]
    change canonRedComul η ≫
      HomologicalComplex.tensorHom (ComonObj.counit (X := C))
        (𝟙 C) = 0
    unfold canonRedComul
    rw [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.sub_comp,
      hΔε, hLε, hRε, hUε, ← hRU]
    abel
  · have hΔε : ComonObj.comul (X := C) ≫
          HomologicalComplex.tensorHom (𝟙 C)
            (ComonObj.counit (X := C)) =
        (HomologicalComplex.rightUnitor
          C).inv :=
      ComonObj.comul_counit C
    have hRε : ((HomologicalComplex.rightUnitor _).inv ≫
            HomologicalComplex.tensorHom (𝟙 C)
              η) ≫
            HomologicalComplex.tensorHom (𝟙 C)
              (ComonObj.counit (X := C)) =
        (HomologicalComplex.rightUnitor _).inv := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, hcounit, HomologicalComplex.tensorHom_id_id]
      rfl
    have hLε : ((HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 C)) ≫
            HomologicalComplex.tensorHom (𝟙 C)
              (ComonObj.counit (X := C)) =
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η
            (ComonObj.counit (X := C)) := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    have hUε : (ComonObj.counit (X := C) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              η) ≫
            HomologicalComplex.tensorHom (𝟙 C)
              (ComonObj.counit (X := C)) =
        (ComonObj.counit (X := C)) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η
            (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) := by
      rw [Category.assoc, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id, hcounit]
    have hLU : (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (ComonObj.counit (X := C)) =
          (ComonObj.counit (X := C)) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) := by
      have hfactor : HomologicalComplex.tensorHom η
              (ComonObj.counit (X := C)) =
            HomologicalComplex.tensorHom
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
              (ComonObj.counit (X := C)) ≫
              HomologicalComplex.tensorHom η
                (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) := by
        rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.id_comp,
          Category.comp_id]
      have hnatL : (HomologicalComplex.leftUnitor _).inv ≫
              HomologicalComplex.tensorHom
                (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
                (ComonObj.counit (X := C)) =
            (ComonObj.counit (X := C)) ≫
              (HomologicalComplex.leftUnitor _).inv :=
        (MonoidalCategory.leftUnitor_inv_naturality _).symm
      rw [hfactor, ← Category.assoc, hnatL, Category.assoc]
    change canonRedComul η ≫
      HomologicalComplex.tensorHom (𝟙 C)
        (ComonObj.counit (X := C)) = 0
    unfold canonRedComul
    rw [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.sub_comp,
      hΔε, hLε, hRε, hUε, ← hLU]
    abel

end CochainComplex
