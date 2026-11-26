/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedOver
public import MathlibExt.CategoryTheory.Comonad.BarResolutionAsphericity

/-!
# Polynomial cotangent augmentation and row contraction

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. For `P=(B→A)` in
`Over A`, the polynomial cotangent simplicial module augments to `A ⊗_B Ω_{B/k}`. In each
degree the augmentation sends `a ⊗ dp` to `a ⊗ d(ε(p))`.

For a polynomial presentation `Free_k(σ) ≅ B`, the variables define an algebra section of the
polynomial counit. The associated right extra degeneracy, lifted over `A` and mapped by
cotangent linearization, contracts the normalized row to its augmentation point. Its
normalized augmentation is therefore a quasi-isomorphism.

## References

* Stacks Project, Sections 92.3 and 92.4.7.
* C. Weibel, *An Introduction to Homological Algebra*, Example 8.6.16.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `P=(B→A)` in `Over A`. The augmented
simplicial `A`-module `polynomialCotangentAugmented k A P` has left object the polynomial
cotangent simplicial model of `P`, point `cotangent k A P = A ⊗_B Ω_{B/k}`, and augmentation
induced by the polynomial-resolution evaluation maps. -/
def polynomialCotangentAugmented (P : Over A) :
    SimplicialObject.Augmented (ModuleCat.{max u v} A) :=
  (SimplicialObject.Augmented.whiskeringObj _ _ (cotangentFunctor.{u, v} k A)).obj
    ((polynomialResolution.{u, v} k P.left).overPoint P.hom)

@[simp]
theorem polynomialCotangentAugmented_left (P : Over A) :
    (polynomialCotangentAugmented.{u, v} k A P).left =
      (polynomialCotangentSimplicialFunctor.{u, v} k A).obj P := rfl

@[simp]
theorem polynomialCotangentAugmented_point (P : Over A) :
    (polynomialCotangentAugmented.{u, v} k A P).right = cotangent k A P := rfl

/-- For a commutative ring `k` and fixed `k`-algebra `A`, `polynomialCotangentAugmentedFunctor k A
: Over A → SimplicialObject.Augmented (ModuleCat A)` sends `P` to its polynomial cotangent
augmented model. A morphism over `A` acts by the polynomial-resolution map lifted over the
augmentation target and then by the cotangent functor. -/
def polynomialCotangentAugmentedFunctor :
    Over A ⥤ SimplicialObject.Augmented (ModuleCat.{max u v} A) where
  obj := polynomialCotangentAugmented.{u, v} k A
  map f := (SimplicialObject.Augmented.whiskeringObj _ _ (cotangentFunctor.{u, v} k A)).map
    (SimplicialObject.Augmented.overPointMap
      (polynomialResolutionMap.{u, v} k f.left) f.w)
  map_id P := by
    let W := SimplicialObject.Augmented.whiskeringObj (Over A) (ModuleCat.{max u v} A)
      (cotangentFunctor.{u, v} k A)
    have h : SimplicialObject.Augmented.overPointMap
        ((polynomialResolutionFunctor.{u, v} k).map (𝟙 P.left)) (by exact Category.id_comp P.hom) =
        𝟙 ((polynomialResolution.{u, v} k P.left).overPoint P.hom) := by
      apply SimplicialObject.Augmented.hom_ext
      · apply NatTrans.ext
        funext i
        apply Over.OverMorphism.ext
        exact congrArg (fun f => f.left.app i)
          ((polynomialResolutionFunctor.{u, v} k).map_id P.left)
      · apply Over.OverMorphism.ext
        rfl
    exact (congrArg W.map h).trans (W.map_id _)
  map_comp {P Q T} f g := by
    let W := SimplicialObject.Augmented.whiskeringObj (Over A) (ModuleCat.{max u v} A)
      (cotangentFunctor.{u, v} k A)
    let pf := polynomialResolutionMap.{u, v} k f.left
    let pg := polynomialResolutionMap.{u, v} k g.left
    have h : SimplicialObject.Augmented.overPointMap
        (polynomialResolutionMap.{u, v} k (f ≫ g).left) (f ≫ g).w =
        SimplicialObject.Augmented.overPointMap pf f.w ≫
          SimplicialObject.Augmented.overPointMap pg g.w := by
      apply SimplicialObject.Augmented.hom_ext
      · apply NatTrans.ext
        funext i
        apply Over.OverMorphism.ext
        exact congrArg (fun f => f.left.app i)
          ((polynomialResolutionFunctor.{u, v} k).map_comp f.left g.left)
      · apply Over.OverMorphism.ext
        rfl
    exact (congrArg W.map h).trans (W.map_comp _ _)

@[simp]
theorem polynomialCotangentAugmentedFunctor_map_left {P Q : Over A} (f : P ⟶ Q) :
    ((polynomialCotangentAugmentedFunctor.{u, v} k A).map f).left =
      (polynomialCotangentSimplicialFunctor.{u, v} k A).map f := rfl

@[simp]
theorem polynomialCotangentAugmentedFunctor_map_right {P Q : Over A} (f : P ⟶ Q) :
    ((polynomialCotangentAugmentedFunctor.{u, v} k A).map f).right = cotangentMap.{u, v} k A f := rfl

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `f : P → Q` in `Over A`. For the
simplicial cotangent functor `C` and augmentation `ε`, `C(f) ≫ ε_Q = ε_P ≫ const(cotangentMap
k A f)`. Thus the simplicial augmentation commutes with the induced map on source cotangent
linearizations. -/
@[reassoc]
theorem polynomialCotangentAugmentation_naturality {P Q : Over A} (f : P ⟶ Q) :
    (polynomialCotangentSimplicialFunctor.{u, v} k A).map f ≫
        (polynomialCotangentAugmented.{u, v} k A Q).hom =
      (polynomialCotangentAugmented.{u, v} k A P).hom ≫
        (SimplicialObject.const (ModuleCat.{max u v} A)).map (cotangentMap.{u, v} k A f) := by
  have h := ((polynomialCotangentAugmentedFunctor.{u, v} k A).map f).w
  change (polynomialCotangentSimplicialFunctor.{u, v} k A).map f ≫
      (polynomialCotangentAugmented.{u, v} k A Q).hom =
    (polynomialCotangentAugmented.{u, v} k A P).hom ≫
      (SimplicialObject.const (ModuleCat.{max u v} A)).map (cotangentMap.{u, v} k A f) at h
  exact h

/-- For a commutative ring `k`, a fixed `k`-algebra `A`, `P∈Over A`, and `n : ℕ`,
`polynomialCotangentAugmentationAt k A P n` is the degree-`n` component of the simplicial
augmentation. It maps `A ⊗_{P_n} Ω_{P_n/k}` to `cotangent k A P`, where `P_n` is the
polynomial resolution degree with its map to `A`. -/
def polynomialCotangentAugmentationAt (P : Over A) (n : ℕ) :
    ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj P).obj (op ⦋n⦌) ⟶
      cotangent k A P :=
  (polynomialCotangentAugmented.{u, v} k A P).hom.app (op ⦋n⦌)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P=(B→A)` in `Over A`, and `ε_n:P_n→B` its
degree-`n` polynomial-resolution augmentation. For `a∈A` and `p∈P_n`, the cotangent
augmentation maps `a ⊗ dp` to `a ⊗ d(ε_n(p))` in `A ⊗_B Ω_{B/k}`. This is the equality of
`cotangentTensor` values. -/
theorem polynomialCotangentAugmentationAt_tensor (P : Over A) (n : ℕ)
    (a : A) (p : (polynomialResolution.{u, v} k P.left).left.obj (op ⦋n⦌)) :
    (polynomialCotangentAugmentationAt.{u, v} k A P n).hom
        (cotangentTensor.{u, v} k A (Over.mk
          (((polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌)) ≫ P.hom)) a p) =
      cotangentTensor.{u, v} k A P a
        (((polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌)).hom p) := by
  let e := (polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌)
  let f : Over.mk (e ≫ P.hom) ⟶ P := Over.homMk e rfl
  change (cotangentMap.{u, v} k A f).hom
      (cotangentTensor.{u, v} k A (Over.mk (e ≫ P.hom)) a p) =
    cotangentTensor.{u, v} k A P a (e.hom p)
  exact cotangentMap_tensor.{u, v} k A f a p

/-- For a commutative ring `k`, a `k`-algebra `A`, and `P∈Over A`, the chain map
`polynomialCotangentNormalizedAugmentation k A P` runs from the normalized polynomial
cotangent complex to `cotangent k A P` concentrated in degree zero. It is the Moore inclusion
followed by the alternating-face augmentation of `polynomialCotangentAugmented k A P`. -/
def polynomialCotangentNormalizedAugmentation (P : Over A) :
    (polynomialCotangentChainFunctor k A).obj P ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} A)).obj (cotangent k A P) :=
  inclusionOfMooreComplexMap ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj P) ≫
    AlternatingFaceMapComplex.ε.app (polynomialCotangentAugmented.{u, v} k A P)

variable {A}

/-- Let `k : Type u` be a commutative ring and `σ : Type(max u v)`. The algebra map
`polynomialCounitSection k σ : Free_k(σ) → T(Free_k(σ))` sends the variable indexed by `x∈σ`
to the outer polynomial variable indexed by that same variable `X_x` in `Free_k(σ)`. It is the
free-algebra map of the free/forget adjunction unit. -/
def polynomialCounitSection (σ : Type (max u v)) :
    (free.{u, v} k).obj σ ⟶
      (polynomialComonad.{u, v} k).obj ((free.{u, v} k).obj σ) :=
  (free.{u, v} k).map ((freeForgetAdjunction.{u, v} k).unit.app σ)

@[reassoc]
theorem polynomialCounitSection_counit (σ : Type (max u v)) :
    polynomialCounitSection.{u, v} k σ ≫
      (polynomialComonad.{u, v} k).ε.app ((free.{u, v} k).obj σ) =
      𝟙 ((free.{u, v} k).obj σ) :=
  (freeForgetAdjunction.{u, v} k).left_triangle_components σ

/-- Let `k` be a commutative ring, `P` a `k`-algebra, and `e : Free_k(σ) ≅ P` a polynomial
presentation. The algebra map `polynomialCounitSectionOfIso k P σ e : P → T(P)` is `e.inv ≫
polynomialCounitSection k σ ≫ T.map e.hom`. It transports the free-algebra counit section to
the presented algebra. -/
def polynomialCounitSectionOfIso (P : CommAlgCat.{max u v} k)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P) :
    P ⟶ (polynomialComonad.{u, v} k).obj P :=
  e.inv ≫ polynomialCounitSection.{u, v} k σ ≫
    (polynomialComonad.{u, v} k).map e.hom

@[reassoc]
theorem polynomialCounitSectionOfIso_counit (P : CommAlgCat.{max u v} k)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P) :
    polynomialCounitSectionOfIso.{u, v} k P σ e ≫
      (polynomialComonad.{u, v} k).ε.app P = 𝟙 P := by
  simp only [polynomialCounitSectionOfIso, Category.assoc]
  rw [(polynomialComonad.{u, v} k).ε.naturality e.hom,
    ← Category.assoc (polynomialCounitSection.{u, v} k σ),
    polynomialCounitSection_counit, Category.id_comp, Functor.id_map, Iso.inv_hom_id]

variable (A)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `P∈Over A` with polynomial presentation
`e : Free_k(σ) ≅ P.left`. The augmented polynomial cotangent simplicial module of `P` has a
right extra degeneracy. It is obtained from the transported algebra counit section, the
polynomial-comonad right extra degeneracy, its lift over `P.hom`, and cotangent linearization. -/
def polynomialCotangentRightExtra (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) :
    SimplicialObject.Augmented.RightExtraDegeneracy
      (polynomialCotangentAugmented.{u, v} k A P) :=
  ((Comonad.resolutionRightExtraOfCounitSection (polynomialComonad.{u, v} k) P.left
      (polynomialCounitSectionOfIso.{u, v} k P.left σ e)
      (polynomialCounitSectionOfIso_counit.{u, v} k P.left σ e)).overPoint P.hom).map
    (cotangentFunctor.{u, v} k A)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `P∈Over A` with polynomial presentation
`e : Free_k(σ) ≅ P.left`. There is a chain homotopy equivalence from the normalized polynomial
cotangent row of `P` to `cotangent k A P` concentrated in degree zero. Its forward map is
`polynomialCotangentNormalizedAugmentation k A P`. -/
def polynomialCotangentAugmentationHomotopyEquiv (P : Over A)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P.left) :
    HomotopyEquiv ((polynomialCotangentChainFunctor k A).obj P)
      ((ChainComplex.single₀ (ModuleCat.{max u v} A)).obj (cotangent k A P)) :=
  (polynomialCotangentNormalizationHomotopyEquiv.{u, v} k A P).trans
    (polynomialCotangentRightExtra.{u, v} k A P σ e).homotopyEquiv

@[simp]
theorem polynomialCotangentAugmentationHomotopyEquiv_hom (P : Over A)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P.left) :
    (polynomialCotangentAugmentationHomotopyEquiv k A P σ e).hom =
      polynomialCotangentNormalizedAugmentation.{u, v} k A P := rfl

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `P∈Over A` with polynomial presentation
`e : Free_k(σ) ≅ P.left`. Then `polynomialCotangentNormalizedAugmentation k A P` is a
quasi-isomorphism from the normalized row to its source cotangent linearization in degree
zero, as the forward map of the constructed homotopy equivalence. -/
theorem polynomialCotangentNormalizedAugmentation_quasiIso (P : Over A)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P.left) :
    QuasiIso (polynomialCotangentNormalizedAugmentation.{u, v} k A P) :=
  (polynomialCotangentAugmentationHomotopyEquiv k A P σ e).quasiIso_hom

end CommAlgCat

end
