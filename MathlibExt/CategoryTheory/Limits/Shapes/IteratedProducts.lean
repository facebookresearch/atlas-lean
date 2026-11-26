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

public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Projection and coherence interfaces for iterated products

For `I : Type`, `K : I → Type`, `X : (i : I) → K i → C`, Mathlib provides `piPiIso`

`(∏ᶜ fun i => ∏ᶜ X i) ≅ (∏ᶜ fun p : Σ i, K i => X p.1 p.2)`

The flat product's existence follows from the inner and outer product assumptions.
`HasProduct` expresses mere existence in `Prop`; an instance proof does not encode an
independent choice of product data. Supplying the flat-product existence assumption explicitly
gives the same canonical comparison.

This interface retains all three product assumptions explicitly:

* `[∀ i, HasProduct (X i)]`
* `[HasProduct (fun i => product (X i))]`
* `[HasProduct (fun p : Σ i, K i => X p.1 p.2)]`

It works directly with arbitrary dependent sigma types, including empty fibers. Its named maps
are definitionally the inverse and forward maps of Mathlib's `piPiIso`, and its isomorphism is
definitionally `(piPiIso K X).symm`. Projection, reindexing and associativity interfaces expose
the comparison without changing that data.

## Main definitions

* `chosenPiPiHom` — forward map `∏ᶜ (flat) ⟶ ∏ᶜ fun i => ∏ᶜ X i`, defined as outer `Pi.lift`
  of inner `Pi.lift` of the flat projection at `⟨i, j⟩`.
* `chosenPiPiInv` — reverse map `∏ᶜ fun i => ∏ᶜ X i ⟶ ∏ᶜ (flat)`, defined as flat `Pi.lift`
  of outer then inner projections.
* Projection simp lemmas for both maps.
* `chosenPiPiIso` — the canonical isomorphism built from those maps; both inverse laws are
  proved by `Pi.hom_ext` and the projection lemmas.
* `chosenPiPiHom_assoc` — coherence of the two ways to regroup a
  three-level product, for any flat reassociation map with the expected projection law.

The naming `chosen` records the explicit inner, outer and flat product assumptions; it does not
assert that different proofs of product existence select different data.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe w₁ w₂ w₃ v u

variable {C : Type u} [Category.{v} C]

noncomputable section

/-- The forward map from a product over a unique index type, expressed using any projection. -/
@[reassoc]
theorem productUniqueIso_hom_π {β : Type w₁} [Unique β] (f : β → C) (b : β) :
    (productUniqueIso f).hom =
      Pi.π f b ≫ eqToHom (congrArg f (Subsingleton.allEq b default)) := by
  obtain rfl := Subsingleton.allEq b default
  simp [productUniqueIso_hom]

/-- Forward comparison: flat product over `Σ i, K i` to iterated product `∏ᶜ i, ∏ᶜ j, X i j`.

It is `Pi.lift (outer)` of `Pi.lift (inner)` of the flat projection at `⟨i, j⟩`,
definitionally the inverse map of Mathlib's `piPiIso` with all product assumptions explicit. -/
def chosenPiPiHom {I : Type w₁} {K : I → Type w₂} {X : (i : I) → K i → C}
    [∀ i, HasProduct (X i)]
    [HasProduct (fun i => ∏ᶜ X i)]
    [HasProduct (fun p : (Σ i, K i) => X p.1 p.2)] :
    (∏ᶜ fun p : (Σ i, K i) => X p.1 p.2) ⟶ (∏ᶜ fun i => ∏ᶜ X i) :=
  Pi.lift (f := fun i => ∏ᶜ X i) fun i =>
    Pi.lift (f := X i) fun j =>
      Pi.π (fun p : (Σ i, K i) => X p.1 p.2) ⟨i, j⟩

/-- Reverse comparison: iterated product to flat product over `Σ i, K i`.

It is `Pi.lift (flat)` of outer projection followed by inner projection. -/
def chosenPiPiInv {I : Type w₁} {K : I → Type w₂} {X : (i : I) → K i → C}
    [∀ i, HasProduct (X i)]
    [HasProduct (fun i => ∏ᶜ X i)]
    [HasProduct (fun p : (Σ i, K i) => X p.1 p.2)] :
    (∏ᶜ fun i => ∏ᶜ X i) ⟶ (∏ᶜ fun p : (Σ i, K i) => X p.1 p.2) :=
  Pi.lift (f := fun p : (Σ i, K i) => X p.1 p.2) fun p =>
    Pi.π (fun i => ∏ᶜ X i) p.1 ≫ Pi.π (X p.1) p.2

@[reassoc (attr := simp)]
theorem chosenPiPiHom_π {I : Type w₁} {K : I → Type w₂} {X : (i : I) → K i → C}
    [∀ i, HasProduct (X i)]
    [HasProduct (fun i => ∏ᶜ X i)]
    [HasProduct (fun p : (Σ i, K i) => X p.1 p.2)]
    (i : I) :
    chosenPiPiHom (I := I) (K := K) (X := X) ≫ Pi.π (fun i => ∏ᶜ X i) i =
      Pi.lift (f := X i) fun j => Pi.π (fun p : (Σ i, K i) => X p.1 p.2) ⟨i, j⟩ := by
  simp only [chosenPiPiHom, Pi.lift_comp_π]

@[reassoc]
theorem chosenPiPiHom_π_π {I : Type w₁} {K : I → Type w₂} {X : (i : I) → K i → C}
    [∀ i, HasProduct (X i)]
    [HasProduct (fun i => ∏ᶜ X i)]
    [HasProduct (fun p : (Σ i, K i) => X p.1 p.2)]
    (i : I) (j : K i) :
    chosenPiPiHom (I := I) (K := K) (X := X) ≫ Pi.π (fun i => ∏ᶜ X i) i ≫ Pi.π (X i) j =
      Pi.π (fun p : (Σ i, K i) => X p.1 p.2) ⟨i, j⟩ := by
  calc
    chosenPiPiHom (I := I) (K := K) (X := X) ≫ Pi.π (fun i => ∏ᶜ X i) i ≫ Pi.π (X i) j
        = (chosenPiPiHom (I := I) (K := K) (X := X) ≫
            Pi.π (fun i => ∏ᶜ X i) i) ≫ Pi.π (X i) j := by
          rw [Category.assoc]
    _ = (Pi.lift (f := X i) fun j => Pi.π (fun p : (Σ i, K i) => X p.1 p.2) ⟨i, j⟩) ≫
            Pi.π (X i) j := by
          rw [chosenPiPiHom_π]
    _ = Pi.π (fun p : (Σ i, K i) => X p.1 p.2) ⟨i, j⟩ := by
          rw [Pi.lift_comp_π]

@[reassoc (attr := simp)]
theorem chosenPiPiInv_π {I : Type w₁} {K : I → Type w₂} {X : (i : I) → K i → C}
    [∀ i, HasProduct (X i)]
    [HasProduct (fun i => ∏ᶜ X i)]
    [HasProduct (fun p : (Σ i, K i) => X p.1 p.2)]
    (p : (Σ i, K i)) :
    chosenPiPiInv (I := I) (K := K) (X := X) ≫
        Pi.π (fun p : (Σ i, K i) => X p.1 p.2) p =
      Pi.π (fun i => ∏ᶜ X i) p.1 ≫ Pi.π (X p.1) p.2 := by
  simp only [chosenPiPiInv, Pi.lift_comp_π]

/-- Canonical isomorphism from the flat product to the iterated product, with all inner,
outer and flat product assumptions explicit.

The complete isomorphism is definitionally `(piPiIso K X).symm`. Both inverse laws follow
from the product projection equations. -/
noncomputable def chosenPiPiIso {I : Type w₁} {K : I → Type w₂} {X : (i : I) → K i → C}
    [∀ i, HasProduct (X i)]
    [HasProduct (fun i => ∏ᶜ X i)]
    [HasProduct (fun p : (Σ i, K i) => X p.1 p.2)] :
    (∏ᶜ fun p : (Σ i, K i) => X p.1 p.2) ≅ (∏ᶜ fun i => ∏ᶜ X i) where
  hom := chosenPiPiHom
  inv := chosenPiPiInv
  hom_inv_id := by
    ext ⟨i, j⟩
    simp only [Category.assoc, Category.id_comp, chosenPiPiInv_π, chosenPiPiHom_π_π]
  inv_hom_id := by
    ext i : 1
    ext j
    simp only [Category.assoc, Category.id_comp, chosenPiPiHom_π, Pi.lift_comp_π, chosenPiPiInv_π]

/-- Associativity coherence for three-level products with every product assumption explicit.

The map `reassoc` compares the right-associated and left-associated flat triple products.
It need not be presented as a particular reindexing construction: the leaf projection law
`hreassoc` completely characterizes the coherence needed here. The conclusion says that
flattening the last level and then regrouping the first two levels agrees with first grouping
the last two levels and then applying the local flat-to-iterated comparisons. -/
theorem chosenPiPiHom_assoc
    {I : Type w₁} {K : I → Type w₂} {L : (i : I) → K i → Type w₃}
    {X : (i : I) → (j : K i) → L i j → C}
    [∀ i j, HasProduct (X i j)]
    [∀ i, HasProduct (fun j ↦ ∏ᶜ X i j)]
    [HasProduct (fun i ↦ ∏ᶜ fun j ↦ ∏ᶜ X i j)]
    [∀ i, HasProduct (fun p : Σ j, L i j ↦ X i p.1 p.2)]
    [HasProduct (fun i ↦ ∏ᶜ fun p : Σ j, L i j ↦ X i p.1 p.2)]
    [HasProduct (fun p : Σ i, K i ↦ ∏ᶜ X p.1 p.2)]
    [HasProduct (fun q : Σ p : Σ i, K i, L p.1 p.2 ↦ X q.1.1 q.1.2 q.2)]
    [HasProduct (fun q : Σ i, Σ j, L i j ↦ X q.1 q.2.1 q.2.2)]
    (reassoc :
      (∏ᶜ fun q : Σ i, Σ j, L i j ↦ X q.1 q.2.1 q.2.2) ⟶
        ∏ᶜ fun q : Σ p : Σ i, K i, L p.1 p.2 ↦ X q.1.1 q.1.2 q.2)
    (hreassoc : ∀ i j k,
      reassoc ≫
          Pi.π (fun q : Σ p : Σ i, K i, L p.1 p.2 ↦ X q.1.1 q.1.2 q.2)
            ⟨⟨i, j⟩, k⟩ =
        Pi.π (fun q : Σ i, Σ j, L i j ↦ X q.1 q.2.1 q.2.2)
          ⟨i, ⟨j, k⟩⟩) :
    reassoc ≫
        chosenPiPiHom
          (X := fun (p : Σ i, K i) (k : L p.1 p.2) ↦ X p.1 p.2 k) ≫
        chosenPiPiHom (X := fun i j ↦ ∏ᶜ X i j) =
      chosenPiPiHom
          (X := fun i (p : Σ j, L i j) ↦ X i p.1 p.2) ≫
        Pi.map (fun i ↦ chosenPiPiHom (X := X i)) := by
  apply Pi.hom_ext
  intro i
  apply Pi.hom_ext
  intro j
  apply Pi.hom_ext
  intro k
  simp only [Category.assoc, chosenPiPiHom_π_π, Pi.map_π, hreassoc]

/-- General naturality/extensionality criterion for `chosenPiPiHom` at the raw
dependent-product level, oriented for direct source-indexed specialization.

We are given source and target nested families

* `X : (i : I) → K i → C` with inner, outer and flat product assumptions,
* `Y : (i' : I') → K' i' → C` with inner, outer and flat product assumptions,

outer and fiber equivalences `eI : I ≃ I'` and `eK : ∀ i, K i ≃ K' (eI i)`,
component morphisms `f i j : X i j ⟶ Y (eI i) (eK i j)`,
and arbitrary comparison maps

* `flatMap : ∏ᶜ (flat X) ⟶ ∏ᶜ (flat Y)`,
* `iterMap : ∏ᶜ (iter X) ⟶ ∏ᶜ (iter Y)`,

with projection hypotheses indexed by source `i j`:

* `flatMap ≫ π_Y ⟨eI i, eK i j⟩ = π_X ⟨i, j⟩ ≫ f i j`,
* `iterMap ≫ π_Y (eI i) ≫ π_Y (eK i j) = π_X i ≫ π_X j ≫ f i j`.

Then `flatMap ≫ chosenPiPiHom_Y = chosenPiPiHom_X ≫ iterMap`.

The source-oriented orientation `I ≃ I'` and `K i ≃ K' (eI i)` is chosen so that
applications whose components are naturally indexed by source positions `i j`
specialize without transports: the hypotheses `hFlat` and `hIter` already use
source indices `i j` on both sides. The proof uses two `Pi.hom_ext`
applications followed by surjectivity of `eI` and `eK` to reduce an arbitrary
target pair `i' j'` to a source pair `i j`. We reuse `chosenPiPiHom_π_π`
projection lemmas and `Pi.hom_ext`. -/
theorem chosenPiPiHom_naturality {I I' : Type w₁} {K : I → Type w₂} {K' : I' → Type w₂}
    {X : (i : I) → K i → C} {Y : (i' : I') → K' i' → C}
    [∀ i, HasProduct (X i)]
    [HasProduct (fun i => ∏ᶜ X i)]
    [HasProduct (fun p : (Σ i, K i) => X p.1 p.2)]
    [∀ i', HasProduct (Y i')]
    [HasProduct (fun i' => ∏ᶜ Y i')]
    [HasProduct (fun p' : (Σ i', K' i') => Y p'.1 p'.2)]
    (eI : I ≃ I') (eK : ∀ i, K i ≃ K' (eI i))
    (f : ∀ i j, X i j ⟶ Y (eI i) (eK i j))
    (flatMap : (∏ᶜ fun p : (Σ i, K i) => X p.1 p.2) ⟶
      (∏ᶜ fun p' : (Σ i', K' i') => Y p'.1 p'.2))
    (iterMap : (∏ᶜ fun i => ∏ᶜ X i) ⟶ (∏ᶜ fun i' => ∏ᶜ Y i'))
    (hFlat : ∀ i j,
      flatMap ≫ Pi.π (fun p' : (Σ i', K' i') => Y p'.1 p'.2) ⟨eI i, eK i j⟩ =
        Pi.π (fun p : (Σ i, K i) => X p.1 p.2) ⟨i, j⟩ ≫ f i j)
    (hIter : ∀ i j,
      iterMap ≫ Pi.π (fun i' => ∏ᶜ Y i') (eI i) ≫ Pi.π (Y (eI i)) (eK i j) =
        Pi.π (fun i => ∏ᶜ X i) i ≫ Pi.π (X i) j ≫ f i j) :
    flatMap ≫ chosenPiPiHom (X := Y) = chosenPiPiHom (X := X) ≫ iterMap := by
  apply Pi.hom_ext
  intro i'
  apply Pi.hom_ext
  intro j'
  obtain ⟨i, rfl⟩ := eI.surjective i'
  obtain ⟨j, rfl⟩ := (eK i).surjective j'
  calc
    ((flatMap ≫ chosenPiPiHom) ≫ Pi.π (fun i' => ∏ᶜ Y i') (eI i)) ≫
          Pi.π (Y (eI i)) (eK i j)
        = flatMap ≫ (chosenPiPiHom ≫ Pi.π (fun i' => ∏ᶜ Y i') (eI i) ≫
          Pi.π (Y (eI i)) (eK i j)) := by
          simp only [Category.assoc]
    _ = flatMap ≫ Pi.π (fun p' : (Σ i', K' i') => Y p'.1 p'.2) ⟨eI i, eK i j⟩ := by
          rw [chosenPiPiHom_π_π]
    _ = Pi.π (fun p : (Σ i, K i) => X p.1 p.2) ⟨i, j⟩ ≫ f i j := by
          rw [hFlat]
    _ = (chosenPiPiHom ≫ Pi.π (fun i => ∏ᶜ X i) i ≫ Pi.π (X i) j) ≫ f i j := by
          rw [chosenPiPiHom_π_π]
    _ = chosenPiPiHom ≫ (Pi.π (fun i => ∏ᶜ X i) i ≫ Pi.π (X i) j ≫ f i j) := by
          simp only [Category.assoc]
    _ = chosenPiPiHom ≫
          (iterMap ≫ Pi.π (fun i' => ∏ᶜ Y i') (eI i) ≫ Pi.π (Y (eI i)) (eK i j)) := by
          rw [hIter]
    _ = ((chosenPiPiHom ≫ iterMap) ≫ Pi.π (fun i' => ∏ᶜ Y i') (eI i)) ≫
          Pi.π (Y (eI i)) (eK i j) := by
          simp only [Category.assoc]

end

end CategoryTheory.Limits
