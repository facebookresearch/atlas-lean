/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarCoefficientComparison

/-!
# Resolution independence of coefficient Hochschild chains

Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Its enveloping bar is a projective resolution
of the regular left E-module A, where E = A ⊗[k] Aᵐᵒᵖ acts by
(a ⊗ bᵐᵒᵖ) • x = axb. It is chain homotopy equivalent to every
projective E-resolution P of that same lifted regular module, through
maps covering the multiplication augmentation.

Let M be an arbitrary A-bimodule with commuting k-linear actions.
The right E-action m · (a ⊗ bᵐᵒᵖ) = bma defines the additive functor
F_M(X) = M ⊗_E X. Applying F_M to the resolution comparison gives
a chain homotopy equivalence C_*(A,M) ≃ F_M(P). The bar identification
sends [m ⊗ (a_0 ⊗ ⋯ ⊗ a_{n+1})] to
(a_{n+1} m a_0) ⊗ a_1 ⊗ ⋯ ⊗ a_n; its inverse inserts two outer units.

The induced homology isomorphism agrees with the left-derived functor
comparison and is natural in augmentation-preserving resolution maps.
The source E-module universe is max{u,v} and the coefficient k-module
universe is max{u,v,w}. No flatness condition is imposed on M.

References: J.-L. Loday, Cyclic Homology, §1.1; C. A. Weibel,
An Introduction to Homological Algebra, §2.2, for comparison of
projective resolutions.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  [Module.Projective k A]

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
For any projective resolution P of the lifted regular E-module A,
the enveloping bar resolution is chain homotopy equivalent to P.
The two comparison maps cover the identity of the augmentation target. -/
def envelopingBarResolutionComparison
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    HomotopyEquiv (envelopingBar k A) P.complex :=
  ProjectiveResolution.homotopyEquiv (envelopingBarProjectiveResolution k A) P

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
For a projective E-resolution P → A and the bar-to-P comparison c_P,
the augmentation square is π_P c_P = ε_bar, where ε_bar
is multiplication in bar degree zero and zero in positive degrees. -/
@[reassoc]
theorem envelopingBarResolutionComparison_hom_π
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (envelopingBarResolutionComparison k A P).hom ≫ P.π =
      envelopingBarAugmentationMap k A :=
  ProjectiveResolution.homotopyEquiv_hom_π (envelopingBarProjectiveResolution k A) P

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
For a projective E-resolution P → A and the inverse comparison
g_P : P → bar, the augmentation square is ε_bar g_P = π_P. -/
@[reassoc]
theorem envelopingBarResolutionComparison_inv_π
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (envelopingBarResolutionComparison k A P).inv ≫ envelopingBarAugmentationMap k A = P.π :=
  ProjectiveResolution.homotopyEquiv_inv_π (envelopingBarProjectiveResolution k A) P

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
For a projective E-resolution P → A, every chain map
f : bar → P satisfying π_P f = ε_bar is chain homotopic to
the bar-to-P comparison c_P. -/
def envelopingBarResolutionComparisonLiftHomotopy
    (P : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : envelopingBar k A ⟶ P.complex)
    (hf : f ≫ P.π = envelopingBarAugmentationMap k A) :
    Homotopy f (envelopingBarResolutionComparison k A P).hom :=
  ProjectiveResolution.liftHomotopy (𝟙 (regularEnvelopingTarget k A))
    (P := envelopingBarProjectiveResolution k A) (Q := P) f
    (envelopingBarResolutionComparison k A P).hom
    (by
      simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
      have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
        (regularEnvelopingTarget k A)
      erw [htarget, Category.comp_id]
      exact hf)
    (by
      simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
      have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
        (regularEnvelopingTarget k A)
      erw [htarget, Category.comp_id]
      exact envelopingBarResolutionComparison_hom_π k A P)

variable (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Let k be commutative, A an associative unital k-algebra, and M an
A-bimodule with commuting k-linear left and right actions. Put
E = A ⊗[k] Aᵐᵒᵖ and F_M(X) = M ⊗_E X, with
m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P of the lifted regular module A,
the coefficient resolution complex is F_M(P) degree by degree,
with differential F_M(d_P). It is a k-module chain complex in
universe max{u,v,w}. -/
def coefficientResolutionTensorComplex
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, applying F_M to the bar/P
comparison gives a chain homotopy equivalence
F_M(bar) ≃ F_M(P). Additivity of F_M transports the two chain
homotopies. -/
def coefficientResolutionTensorComparison
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    HomotopyEquiv (coefficientTensorComplex k A M) (coefficientResolutionTensorComplex k A M P) :=
  (coefficientTensorFunctor k A M).mapHomotopyEquiv (envelopingBarResolutionComparison k A P)

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, let c_P : bar → P be its
augmentation-preserving comparison. The forward map of
F_M(bar) ≃ F_M(P) is the chain map F_M(c_P). -/
theorem coefficientResolutionTensorComparison_hom
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientResolutionTensorComparison k A M P).hom =
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingBarResolutionComparison k A P).hom := rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, let g_P : P → bar be the
inverse resolution comparison. The inverse map of
F_M(bar) ≃ F_M(P) is F_M(g_P). -/
theorem coefficientResolutionTensorComparison_inv
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientResolutionTensorComparison k A M P).inv =
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingBarResolutionComparison k A P).inv := rfl

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For every projective E-resolution P of the lifted regular module A,
the Hochschild chain complex C_*(A,M) is chain homotopy equivalent
to F_M(P). The equivalence uses the balanced bar identification
[m ⊗ (a_0 ⊗ ⋯ ⊗ a_{n+1})] ↦
(a_{n+1} m a_0) ⊗ a_1 ⊗ ⋯ ⊗ a_n. -/
def coefficientHochschildResolutionComparison
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    HomotopyEquiv (ModuleCat.Algebra.Hochschild.chainComplex k A M)
      (coefficientResolutionTensorComplex k A M P) :=
  (HomotopyEquiv.ofIso (coefficientTensorChainIso k A M).symm).trans
    (coefficientResolutionTensorComparison k A M P)

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, the forward map
C_*(A,M) → F_M(P) first sends
m ⊗ a_1 ⊗ ⋯ ⊗ a_n to
[m ⊗ (1 ⊗ a_1 ⊗ ⋯ ⊗ a_n ⊗ 1)]
and then applies F_M to the bar-to-P comparison. -/
theorem coefficientHochschildResolutionComparison_hom
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientHochschildResolutionComparison k A M P).hom =
      (coefficientTensorChainIso k A M).inv ≫
        ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (envelopingBarResolutionComparison k A P).hom := rfl

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, the inverse map
F_M(P) → C_*(A,M) first applies F_M to P → bar and then
uses the bar identification
[m ⊗ (a_0 ⊗ ⋯ ⊗ a_{n+1})] ↦
(a_{n+1} m a_0) ⊗ a_1 ⊗ ⋯ ⊗ a_n. -/
theorem coefficientHochschildResolutionComparison_inv
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientHochschildResolutionComparison k A M P).inv =
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingBarResolutionComparison k A P).inv ≫ (coefficientTensorChainIso k A M).hom := rfl

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
Let P → A be a projective E-resolution and f : bar → P a chain map
with π_P f = ε_bar. Insert outer units into Hochschild chains and
then apply F_M(f). This chain map is homotopic to the constructed
comparison C_*(A,M) → F_M(P). -/
def coefficientHochschildResolutionComparisonLiftHomotopy
    (P : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : envelopingBar k A ⟶ P.complex)
    (hf : f ≫ P.π = envelopingBarAugmentationMap k A) :
    Homotopy ((coefficientTensorChainIso k A M).inv ≫
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map f)
      (coefficientHochschildResolutionComparison k A M P).hom :=
  ((coefficientTensorFunctor k A M).mapHomotopy
    (envelopingBarResolutionComparisonLiftHomotopy k A P f hf)).compLeft
      (coefficientTensorChainIso k A M).inv

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
Every projective E-resolution P → A gives a k-module isomorphism
HH_n(A,M) ≅ H_n(F_M(P)) for n ≥ 0. It is induced by the
constructed Hochschild-to-resolution chain homotopy equivalence. -/
def coefficientHochschildHomologyIsoForResolution
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.chainComplex k A M).homology n ≅
      (coefficientResolutionTensorComplex k A M P).homology n :=
  (coefficientHochschildResolutionComparison k A M P).toHomologyIso n

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, the forward map of
HH_n(A,M) ≅ H_n(F_M(P)) is H_n of the constructed chain map
C_*(A,M) → F_M(P). -/
theorem coefficientHochschildHomologyIsoForResolution_hom
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (coefficientHochschildHomologyIsoForResolution k A M P n).hom =
      HomologicalComplex.homologyMap (coefficientHochschildResolutionComparison k A M P).hom n := rfl

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, the inverse map of
HH_n(A,M) ≅ H_n(F_M(P)) is H_n of the constructed inverse
chain map F_M(P) → C_*(A,M). -/
theorem coefficientHochschildHomologyIsoForResolution_inv
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (coefficientHochschildHomologyIsoForResolution k A M P n).inv =
      HomologicalComplex.homologyMap (coefficientHochschildResolutionComparison k A M P).inv n := rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
Let P → A be a projective E-resolution and write
ι_P : L_n F_M(A) ≅ H_n(F_M(P)) for its resolution isomorphism,
with ι_bar defined by the bar resolution. Then
H_n(F_M(c_P)) = ι_P ι_bar⁻¹, where c_P : bar → P is the
augmentation-preserving comparison. -/
theorem coefficientResolutionTensorComparison_homology
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    ((envelopingBarProjectiveResolution k A).isoLeftDerivedObj (coefficientTensorFunctor k A M) n).inv ≫
        (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom =
      HomologicalComplex.homologyMap (coefficientResolutionTensorComparison k A M P).hom n := by
  have hπ := congrArg (fun f => f.f 0) (envelopingBarResolutionComparison_hom_π k A P)
  have hcomm : (envelopingBarResolutionComparison k A P).hom.f 0 ≫ P.π.f 0 =
      (envelopingBarProjectiveResolution k A).π.f 0 ≫ 𝟙 (regularEnvelopingTarget k A) := by
    simp only [HomologicalComplex.comp_f, Category.comp_id, envelopingBarProjectiveResolution_π] at hπ ⊢
    exact hπ
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    (𝟙 (regularEnvelopingTarget k A)) (envelopingBarProjectiveResolution k A) P
    (envelopingBarResolutionComparison k A P).hom hcomm (coefficientTensorFunctor k A M) n
  apply (cancel_epi
    ((envelopingBarProjectiveResolution k A).isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hid := ((coefficientTensorFunctor k A M).leftDerived n).map_id (regularEnvelopingTarget k A)
  erw [hid, Category.id_comp] at h
  exact h

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
For a projective E-resolution P → A, the isomorphism
HH_n(A,M) ≅ H_n(F_M(P)) equals the composite
HH_n(A,M) ≅ L_n F_M(A) ≅ H_n(F_M(P)), using the bar
identification for the first map and P for the second. -/
theorem coefficientHochschildHomologyIsoForResolution_derived
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (coefficientHochschildHomologyIsoDerived k A M n).hom ≫
        (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom =
      (coefficientHochschildHomologyIsoForResolution k A M P n).hom := by
  change (HomologicalComplex.homologyMap (coefficientTensorChainIso k A M).inv n ≫
      ((envelopingBarProjectiveResolution k A).isoLeftDerivedObj
        (coefficientTensorFunctor k A M) n).inv) ≫
      (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom = _
  erw [Category.assoc, coefficientResolutionTensorComparison_homology,
    ← HomologicalComplex.homologyMap_comp]
  rfl

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
Let P,Q be projective E-resolutions of the lifted regular module A,
and let f : P → Q satisfy π_Q f = π_P. The composite
C_*(A,M) → F_M(P) → F_M(Q) is chain homotopic to the
constructed comparison C_*(A,M) → F_M(Q). -/
def coefficientHochschildResolutionComparisonNaturalityHomotopy
    (P Q : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π) :
    Homotopy ((coefficientHochschildResolutionComparison k A M P).hom ≫
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map f)
      (coefficientHochschildResolutionComparison k A M Q).hom := by
  have h := ProjectiveResolution.liftHomotopy (𝟙 (regularEnvelopingTarget k A))
    (P := envelopingBarProjectiveResolution k A) (Q := Q)
    ((envelopingBarResolutionComparison k A P).hom ≫ f)
    (envelopingBarResolutionComparison k A Q).hom
    (by
        simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
        have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
          (regularEnvelopingTarget k A)
        erw [htarget, Category.comp_id]
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun a => (envelopingBarResolutionComparison k A P).hom ≫ a) hf).trans
            (envelopingBarResolutionComparison_hom_π k A P)))
    (by
        simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
        have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
          (regularEnvelopingTarget k A)
        erw [htarget, Category.comp_id]
        exact envelopingBarResolutionComparison_hom_π k A Q)
  have hmap := ((coefficientTensorFunctor k A M).mapHomotopy h).compLeft (coefficientTensorChainIso k A M).inv
  let F := (coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)
  have hx : ((coefficientTensorChainIso k A M).inv ≫ F.map (envelopingBarResolutionComparison k A P).hom) ≫
      F.map f = (coefficientTensorChainIso k A M).inv ≫ F.map ((envelopingBarResolutionComparison k A P).hom ≫ f) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun g => (coefficientTensorChainIso k A M).inv ≫ g)
        (F.map_comp (envelopingBarResolutionComparison k A P).hom f).symm)
  exact (Homotopy.ofEq hx).trans hmap

/-- Let k be a commutative ring and A an associative unital k-algebra
projective as a k-module. Put E = A ⊗[k] Aᵐᵒᵖ, and view A as
the regular left E-module with (a ⊗ bᵐᵒᵖ) • x = axb.
Let M be an A-bimodule with commuting k-linear actions and put
F_M(X) = M ⊗_E X using m · (a ⊗ bᵐᵒᵖ) = bma.
Let P,Q be projective E-resolutions of the lifted regular module A,
and let f : P → Q satisfy π_Q f = π_P. If E_P and E_Q denote
the constructed homology isomorphisms, then
H_n(F_M(f)) E_P = E_Q. This is the commuting square from
HH_n(A,M) to the two coefficient-resolution homologies. -/
@[reassoc]
theorem coefficientHochschildHomologyIsoForResolution_naturality
    (P Q : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π) (n : ℕ) :
    (coefficientHochschildHomologyIsoForResolution k A M P n).hom ≫
      HomologicalComplex.homologyMap
        (((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n =
      (coefficientHochschildHomologyIsoForResolution k A M Q n).hom := by
  erw [coefficientHochschildHomologyIsoForResolution_hom,
    coefficientHochschildHomologyIsoForResolution_hom, ← HomologicalComplex.homologyMap_comp]
  exact (coefficientHochschildResolutionComparisonNaturalityHomotopy k A M P Q f hf).homologyMap_eq n

end ModuleCat.Algebra.Hochschild.AdjacentBar
