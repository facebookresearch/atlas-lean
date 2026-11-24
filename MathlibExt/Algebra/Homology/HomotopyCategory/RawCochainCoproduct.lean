/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomComplexCoproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Raw cochains out of a complex coproduct

Evaluation preserves the coproduct of complexes. Descending each homogeneous component therefore
constructs a raw cochain, without assuming that the component families are closed. Its
differential and compositions are detected on the literal coproduct inclusions.

Restriction to the summands and componentwise descent give inverse additive maps. Source
naturality uses the `Sigma.map`; degree-zero complex-map families agree with the `Sigma.desc`. All
degrees remain arbitrary integers, including in the internal Hom differential formula.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex.Cochain

universe u v w

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {J : Type w} [HasColimitsOfShape (Discrete J) D]
variable (F : J → CochainComplex D ℤ)

/--
Descend a homogeneous family from the coproduct of complexes. No differential compatibility of the
family is a premise.
-/
noncomputable def coproductDesc {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) : Cochain (∐ F) A d :=
  Cochain.mk fun p q hpq =>
    (isColimitOfPreserves
      (HomologicalComplex.eval D (ComplexShape.up ℤ) p)
      (colimit.isColimit (Discrete.functor F))).desc
      { pt := A.X q
        ι := Discrete.natTrans (fun j => (ψ j.as).v p q hpq) }

/--
The degreewise inclusion law uses the component of the complex-coproduct inclusion. Both component
degrees may be negative.
-/
theorem coproductDesc_ι_v {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (j : J)
    (p q : ℤ) (hpq : p + d = q) :
    (Sigma.ι F j).f p ≫ (coproductDesc F d ψ).v p q hpq =
      (ψ j).v p q hpq := by
  simp only [coproductDesc, mk_v]
  exact (isColimitOfPreserves
    (HomologicalComplex.eval D (ComplexShape.up ℤ) p)
    (colimit.isColimit (Discrete.functor F))).fac
      { pt := A.X q
        ι := Discrete.natTrans (fun i => (ψ i.as).v p q hpq) }
      (Discrete.mk j)

/-- Each complex-coproduct inclusion recovers its specified raw cochain, in every integer degree. -/
theorem coproductDesc_ι {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (j : J) :
    (ofHom (Sigma.ι F j)).comp (coproductDesc F d ψ) (zero_add d) = ψ j := by
  apply Cochain.ext
  intro p q hpq
  simpa only [zero_cochain_comp_v, ofHom_v] using
    coproductDesc_ι_v F d ψ j p q hpq

/--
Precomposing any map into one summand gives its prescribed raw value. This also handles generators
with an unitor prefix.
-/
theorem coproductDesc_ι_comp {A X : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (j : J) (g : X ⟶ F j) :
    (ofHom (g ≫ Sigma.ι F j)).comp (coproductDesc F d ψ) (zero_add d) =
      (ofHom g).comp (ψ j) (zero_add d) := by
  rw [ofHom_comp, comp_assoc_of_first_is_zero_cochain, coproductDesc_ι]

/-- The component equations characterize the entire descended cochain. -/
theorem coproductDesc_unique {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (α : Cochain (∐ F) A d)
    (h : ∀ j : J, (ofHom (Sigma.ι F j)).comp α (zero_add d) = ψ j) :
    α = coproductDesc F d ψ := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  exact (h j).trans (coproductDesc_ι F d ψ j).symm

/-- Descending the restrictions of an arbitrary raw cochain reconstructs
that entire cochain, without requiring differential commutation. -/
theorem coproductDesc_precomp {A : CochainComplex D ℤ} (d : ℤ)
    (α : Cochain (∐ F) A d) :
    coproductDesc F d
      (fun j => (ofHom (Sigma.ι F j)).comp α (zero_add d)) = α := by
  exact (coproductDesc_unique F d
    (fun j => (ofHom (Sigma.ι F j)).comp α (zero_add d)) α (fun _ => rfl)).symm

/-- The zero family descends to the zero raw cochain. -/
theorem coproductDesc_zero {A : CochainComplex D ℤ} (d : ℤ) :
    coproductDesc F d (fun j => (0 : Cochain (F j) A d)) = 0 := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [coproductDesc_ι, Cochain.comp_zero]

/-- Descent is additive on the cochain families. -/
theorem coproductDesc_add {A : CochainComplex D ℤ} (d : ℤ)
    (ψ χ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d (fun j => ψ j + χ j) =
      coproductDesc F d ψ + coproductDesc F d χ := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [Cochain.comp_add, coproductDesc_ι, coproductDesc_ι, coproductDesc_ι]

/-- Descent respects negation, with no nontriviality assumption. -/
theorem coproductDesc_neg {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d (fun j => -(ψ j)) = -(coproductDesc F d ψ) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [Cochain.comp_neg, coproductDesc_ι, coproductDesc_ι]

/-- Differences of raw families descend to the difference of the descended cochains. -/
theorem coproductDesc_sub {A : CochainComplex D ℤ} (d : ℤ)
    (ψ χ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d (fun j => ψ j - χ j) =
      coproductDesc F d ψ - coproductDesc F d χ := by
  simp only [sub_eq_add_neg, coproductDesc_add, coproductDesc_neg]

/-- Vanishing is detected on every summand of the coproduct. -/
theorem coproductDesc_eq_zero_iff {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d ψ = 0 ↔ ∀ j : J, ψ j = 0 := by
  constructor
  · intro h j
    have hj := congrArg
      (fun α : Cochain (∐ F) A d => (ofHom (Sigma.ι F j)).comp α (zero_add d)) h
    simpa only [coproductDesc_ι, Cochain.comp_zero] using hj
  · intro h
    have hψ : ψ = fun _ => 0 := funext h
    rw [hψ, coproductDesc_zero]

/--
Descent commutes with the Hom differential for arbitrary integer source and target degrees,
including off-shape zero differentials.
-/
theorem coproductDesc_δ {A : CochainComplex D ℤ} (d m : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    HomComplex.δ d m (coproductDesc F d ψ) =
      coproductDesc F m (fun j => HomComplex.δ d m (ψ j)) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [← HomComplex.δ_ofHom_comp, coproductDesc_ι, coproductDesc_ι]

/-- A differential vanishes on the descended cochain exactly when it
vanishes on every input summand. This is a conclusion, not a restriction
on which raw families may be descended. -/
theorem coproductDesc_δ_eq_zero_iff {A : CochainComplex D ℤ} (d m : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    HomComplex.δ d m (coproductDesc F d ψ) = 0 ↔
      ∀ j : J, HomComplex.δ d m (ψ j) = 0 := by
  rw [coproductDesc_δ, coproductDesc_eq_zero_iff]

/-- Postcomposition may itself be a raw cochain: closedness is not needed
for the coproduct universal property. -/
theorem coproductDesc_comp {A B : CochainComplex D ℤ} (d e : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (κ : Cochain A B e) :
    coproductDesc F (d + e) (fun j => (ψ j).comp κ rfl) =
      (coproductDesc F d ψ).comp κ rfl := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [coproductDesc_ι, ← comp_assoc_of_first_is_zero_cochain, coproductDesc_ι]

/--
Source naturality descends the maps of summands through the map of coproducts. No
commutative-square witness is extra data.
-/
theorem coproductDesc_map {G : J → CochainComplex D ℤ}
    {A : CochainComplex D ℤ} (a : ∀ j : J, F j ⟶ G j) (d : ℤ)
    (ψ : ∀ j : J, Cochain (G j) A d) :
    (ofHom (CategoryTheory.Limits.Sigma.map a)).comp
        (coproductDesc G d ψ) (zero_add d) =
      coproductDesc F d (fun j => (ofHom (a j)).comp (ψ j) (zero_add d)) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [← comp_assoc_of_first_is_zero_cochain, ← ofHom_comp, Sigma.ι_map,
    coproductDesc_ι_comp, coproductDesc_ι]

/--
For an family of complex morphisms, raw descent agrees with the coproduct morphism. Arbitrary raw
input is still allowed in `coproductDesc`; this identifies its complex-map corner.
-/
theorem coproductDesc_ofHom {A : CochainComplex D ℤ}
    (a : ∀ j : J, F j ⟶ A) :
    coproductDesc F 0 (fun j => ofHom (a j)) = ofHom (Sigma.desc a) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [coproductDesc_ι, ← ofHom_comp, Sigma.ι_comp_desc]

/--
Raw cochains out of the coproduct are additively equivalent to arbitrary families on its summands.
Both inverse identities are proved from the degreewise universal property.
-/
noncomputable def coproductCochainEquiv (A : CochainComplex D ℤ) (d : ℤ) :
    Cochain (∐ F) A d ≃+ (∀ j : J, Cochain (F j) A d) where
  toFun α j := (ofHom (Sigma.ι F j)).comp α (zero_add d)
  invFun ψ := coproductDesc F d ψ
  left_inv α := coproductDesc_precomp F d α
  right_inv ψ := funext (fun j => coproductDesc_ι F d ψ j)
  map_add' α β := funext
    (fun j => Cochain.comp_add (ofHom (Sigma.ι F j)) α β (zero_add d))

/--
The forward additive equivalence is literal restriction by the degree-zero cochain of a coproduct
inclusion.
-/
@[simp]
theorem coproductCochainEquiv_apply {A : CochainComplex D ℤ} (d : ℤ)
    (α : Cochain (∐ F) A d) (j : J) :
    coproductCochainEquiv F A d α j =
      (ofHom (Sigma.ι F j)).comp α (zero_add d) := rfl

/--
The inverse additive equivalence is the componentwise raw descent, rather than a supplied
universal-map field.
-/
@[simp]
theorem coproductCochainEquiv_symm_apply {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    (coproductCochainEquiv F A d).symm ψ = coproductDesc F d ψ := rfl

end CochainComplex.HomComplex.Cochain

end
