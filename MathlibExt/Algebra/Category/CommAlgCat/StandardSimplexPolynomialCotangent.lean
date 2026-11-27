/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ExtraDegeneracyOver
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentPrism
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitting
public import MathlibExt.Algebra.Category.CommAlgCat.AdditiveResolutionCondition

/-!
# Standard-simplex polynomial resolutions and cotangent homotopies

For a variable set σ, pull back the augmented standard d-simplex to obtain σ×Δᵈ→σ. Its extra
degeneracy supplies a section and contraction. Applying the free-algebra functor over a
commutative ring k gives a compatible polynomial resolution of A=k[σ] whose normalized additive
augmentation is a quasi-isomorphism.

Augmentation and the chosen sections construct forward and backward comparisons with the
canonical polynomial resolution. The source prism runs from forward≫backward to identity, while
the canonical right-extra-degeneracy prism runs from identity to backward≫forward. Cotangent
linearization B→A ↦ A ⊗[B] Ω(B/k) and normalized Moore chains give a homotopy equivalence with
those maps. The forward differential-tensor formula is a ⊗ dp ↦ a ⊗ d(Fp).

Tensoring with any A-module M preserves this homotopy equivalence. The set-only construction has
independent carrier universe w. In the algebra construction, k has universe u and σ has stable
carrier max(u,v); coefficients may have any universe t, with tensor output max(t,u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v w t

namespace CommAlgCat.StandardSimplexPolynomialCotangent

section Sets

variable (σ : Type w) (d : ℕ)

/-- For a variable set σ and d∈ℕ, pull back the augmented standard simplex along σ→1. In degree n
this gives σ×HomΔ([n],[d]), augmented to σ by projection. -/
def setResolution : SimplicialObject.Augmented (Type w) :=
  SimplicialObject.Augmented.ExtraDegeneracy.baseChange
    (SSet.Augmented.stdSimplex.{w}.obj ⦋d⦌) (terminal.from σ)

/-- For a variable set σ and d∈ℕ, the augmented diagram σ×Δᵈ→σ inherits the standard simplex's extra
degeneracy, including its augmentation section and contraction. -/
def setExtra : (setResolution σ d).ExtraDegeneracy := by
  let X : SimplicialObject.Augmented (Type w) := SSet.Augmented.stdSimplex.{w}.obj ⦋d⦌
  let p : σ ⟶ X.right := terminal.from σ
  change (SimplicialObject.Augmented.ExtraDegeneracy.baseChange X p).ExtraDegeneracy
  exact SimplicialObject.Augmented.ExtraDegeneracy.baseChangeExtraDegeneracy
    (C := Type w) (A := X) (P := σ) (p := p)
    (ed := SSet.Augmented.StandardSimplex.extraDegeneracy.{w} ⦋d⦌)

/-- For a variable set σ and d∈ℕ, the extra-degeneracy section assigns to x∈σ a degree-zero simplex
above x in the pulled-back standard-simplex diagram. -/
def sourceVariable (x : σ) : (setResolution σ d).left.obj (op ⦋0⦌) :=
  (setExtra σ d).s' x

/-- For a variable set σ and d∈ℕ, the augmentation sends the chosen degree-zero simplex above x∈σ
back to x. -/
@[simp]
theorem sourceVariable_augmentation (x : σ) :
    (setResolution σ d).hom.app (op ⦋0⦌) (sourceVariable σ d x) = x :=
  congrArg (fun f : σ ⟶ σ => f x) ((setExtra σ d).s'_comp_ε)

end Sets

variable (k : Type u) [CommRing k] (σ : Type (max u v)) (d : ℕ)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. The augmentation algebra is the
polynomial k-algebra on σ. -/
abbrev algebra : CommAlgCat.{max u v} k := (free.{u, v} k).obj σ

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Apply the free-algebra functor to
the augmented simplicial set σ×Δᵈ→σ. Its degree-n algebra is k[σ×HomΔ([n],[d])] and its
augmentation target is A. -/
def algebraResolution : SimplicialObject.Augmented (CommAlgCat.{max u v} k) :=
  (SimplicialObject.Augmented.whiskeringObj (Type (max u v)) (CommAlgCat.{max u v} k)
    (free.{u, v} k)).obj (setResolution.{max u v} σ d)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. The polynomial augmented diagram
inherits an extra degeneracy by applying the free-algebra functor to that of σ×Δᵈ→σ. -/
def algebraExtra : (algebraResolution k σ d).ExtraDegeneracy :=
  (setExtra.{max u v} σ d).map (free.{u, v} k)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Identify the augmentation target
of the polynomial standard-simplex diagram with A=k[σ] by the canonical identity map. -/
def sourcePointMap : (algebraResolution k σ d).right ⟶ algebra k σ :=
  eqToHom (show (algebraResolution k σ d).right = algebra k σ from rfl)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Identify the augmentation target
of the canonical polynomial resolution of A with A by its canonical identity map. -/
def targetPointMap : (polynomialResolution k (algebra k σ)).right ⟶ algebra k σ :=
  eqToHom (show (polynomialResolution k (algebra k σ)).right = algebra k σ from rfl)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Regard the polynomial
standard-simplex diagram as an augmented simplicial k-algebra over the fixed target A. -/
def sourceResolution : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj (algebra k σ)) :=
  Over.mk ((algebraResolution k σ d).hom ≫
    (SimplicialObject.const (CommAlgCat.{max u v} k)).map (sourcePointMap k σ d))

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. For x∈σ, take the polynomial
generator indexed by the chosen degree-zero section simplex above x. This is an element of the
source resolution in degree zero. -/
def sourceGenerator (x : σ) : (sourceResolution k σ d).left.obj (op ⦋0⦌) :=
  MvPolynomial.X (sourceVariable.{max u v} σ d x)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. The augmentation of the
degree-zero source generator above x∈σ is the variable Xₓ of A=k[σ]. -/
@[simp]
theorem sourceGenerator_augmentation (x : σ) :
    ((sourceResolution k σ d).hom.app (op ⦋0⦌)).hom (sourceGenerator k σ d x) = MvPolynomial.X x := by
  change MvPolynomial.rename (R := k) ((setResolution.{max u v} σ d).hom.app (op ⦋0⦌))
    (MvPolynomial.X (sourceVariable.{max u v} σ d x)) = _
  exact (MvPolynomial.rename_X (R := k) _ _).trans
    (congrArg (fun y : σ => (MvPolynomial.X y : algebra k σ))
      (sourceVariable_augmentation σ d x))

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. The nondegenerate-simplex
splitting of σ×Δᵈ gives a compatible polynomial splitting of its free-algebra image. -/
def compatibleGenerators : PolynomialSplitting k (sourceResolution k σ d).left :=
  polynomialSplittingOfSSet k (setResolution.{max u v} σ d).left

private def sourceAugmentedIso : algebraResolution k σ d ≅
    augmentedAlgebraOfOver k (algebra k σ) (sourceResolution k σ d) :=
  Comma.isoMk (Iso.refl _) (eqToIso (show
    (algebraResolution k σ d).right = algebra k σ from rfl)) (by
      change (𝟙 _) ≫ ((algebraResolution k σ d).hom ≫
        (SimplicialObject.const (CommAlgCat.{max u v} k)).map (sourcePointMap k σ d)) =
          (algebraResolution k σ d).hom ≫
            (SimplicialObject.const (CommAlgCat.{max u v} k)).map (sourcePointMap k σ d)
      exact Category.id_comp _)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. The extra degeneracy makes the
normalized additive augmentation of the polynomial standard-simplex diagram a quasi-isomorphism. -/
theorem sourceCondition : additiveResolutionCondition k (algebra k σ) (sourceResolution k σ d) := by
  let X := additiveAugmentedResolution k (algebra k σ) (sourceResolution k σ d)
  let ed : X.ExtraDegeneracy :=
    (SimplicialObject.Augmented.ExtraDegeneracy.ofIso (sourceAugmentedIso k σ d)
      (algebraExtra k σ d)).map (algebraModuleFunctor k)
  exact ((DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := X.left)).trans ed.homotopyEquiv).quasiIso_hom

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. The polynomial standard-simplex
diagram has polynomial levels and an additive augmentation quasi-isomorphism, hence defines an
object of the polynomial cotangent-resolution category of A. -/
def sourceResolutionObject : PolynomialCotangentResolutions k (algebra k σ) :=
  polynomialCotangentResolutionOfAdditive k (algebra k σ) (sourceResolution k σ d)
    (fun n => ⟨(setResolution.{max u v} σ d).left.obj (op ⦋n⦌), ⟨Iso.refl _⟩⟩)
    (sourceCondition k σ d)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Take the canonical augmented
polynomial resolution of A, regarded as a simplicial algebra over the constant augmentation
target A. -/
def canonicalResolution : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj (algebra k σ)) :=
  (polynomialResolutionOverFunctor k (algebra k σ)).obj (Over.mk (𝟙 (algebra k σ)))

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The source extra degeneracy lifts to the augmented diagram in Over A and supplies its section
and source contraction. -/
def sourceOverExtra :
    ((algebraResolution k σ d).overPoint (sourcePointMap k σ d)).ExtraDegeneracy :=
  (algebraExtra k σ d).overPoint (sourcePointMap k σ d)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The polynomial presentation A=k[σ] supplies a right extra degeneracy for the canonical
resolution, lifted to the augmented diagram in Over A. -/
def targetOverExtra : SimplicialObject.Augmented.RightExtraDegeneracy
    ((polynomialResolution k (algebra k σ)).overPoint (targetPointMap k σ)) :=
  (polynomialResolutionRightExtraOfPresentation k σ (algebra k σ) (Iso.refl _)).overPoint
    (targetPointMap k σ)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The constant augmentation-point diagrams of P and Q in Over A are naturally identified by the
identity of A. -/
def pointIso :
    (SimplicialObject.const (Over (algebra k σ))).obj
      ((algebraResolution k σ d).overPoint (sourcePointMap k σ d)).right ≅
    (SimplicialObject.const (Over (algebra k σ))).obj
      ((polynomialResolution k (algebra k σ)).overPoint (targetPointMap k σ)).right :=
  (SimplicialObject.const (Over (algebra k σ))).mapIso (eqToIso (by rfl))

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The forward slice map P→Q is the augmentation of P followed by the section of Q's right extra
degeneracy, through the common augmentation point. -/
def overForward : Over.lift (sourceResolution k σ d).left (sourceResolution k σ d).hom ⟶
    Over.lift (canonicalResolution k σ).left (canonicalResolution k σ).hom :=
  ((algebraResolution k σ d).overPoint (sourcePointMap k σ d)).hom ≫
    (pointIso k σ d).hom ≫ (targetOverExtra k σ).section_

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The backward slice comparison Q→P is the augmentation of Q followed by the section of P's
extra degeneracy. The subsequent prism identities make it a homotopy inverse to the forward
comparison. -/
def overBackward : Over.lift (canonicalResolution k σ).left (canonicalResolution k σ).hom ⟶
    Over.lift (sourceResolution k σ d).left (sourceResolution k σ d).hom :=
  ((polynomialResolution k (algebra k σ)).overPoint (targetPointMap k σ)).hom ≫
    (pointIso k σ d).inv ≫ (sourceOverExtra k σ d).section_

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The forward comparison followed by the backward comparison is P's augmentation followed by
its chosen section. -/
theorem forward_backward : overForward k σ d ≫ overBackward k σ d =
    ((algebraResolution k σ d).overPoint (sourcePointMap k σ d)).hom ≫
      (sourceOverExtra k σ d).section_ := by
  have h : (targetOverExtra k σ).section_ ≫
      ((polynomialResolution k (algebra k σ)).overPoint (targetPointMap k σ)).hom = 𝟙 _ :=
    (targetOverExtra k σ).section_comp_augmentation
  let a := ((algebraResolution k σ d).overPoint (sourcePointMap k σ d)).hom
  let s := (targetOverExtra k σ).section_
  let e := ((polynomialResolution k (algebra k σ)).overPoint (targetPointMap k σ)).hom
  let b := (sourceOverExtra k σ d).section_
  let c := pointIso k σ d
  change (a ≫ c.hom ≫ s) ≫ (e ≫ c.inv ≫ b) = a ≫ b
  have hh : s ≫ e = 𝟙 _ := h
  rw [Category.assoc a (c.hom ≫ s) (e ≫ c.inv ≫ b),
    Category.assoc c.hom s (e ≫ c.inv ≫ b), ← Category.assoc s e (c.inv ≫ b),
    hh, Category.id_comp, Iso.hom_inv_id_assoc]

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The backward comparison followed by the forward comparison is Q's augmentation followed by
its chosen right-extra-degeneracy section. -/
theorem backward_forward : overBackward k σ d ≫ overForward k σ d =
    ((polynomialResolution k (algebra k σ)).overPoint (targetPointMap k σ)).hom ≫
      (targetOverExtra k σ).section_ := by
  have h : (sourceOverExtra k σ d).section_ ≫
      ((algebraResolution k σ d).overPoint (sourcePointMap k σ d)).hom = 𝟙 _ :=
    (sourceOverExtra k σ d).section_comp_hom
  let a := ((polynomialResolution k (algebra k σ)).overPoint (targetPointMap k σ)).hom
  let s := (sourceOverExtra k σ d).section_
  let e := ((algebraResolution k σ d).overPoint (sourcePointMap k σ d)).hom
  let b := (targetOverExtra k σ).section_
  let c := pointIso k σ d
  change (a ≫ c.inv ≫ s) ≫ (e ≫ c.hom ≫ b) = a ≫ b
  have hh : s ≫ e = 𝟙 _ := h
  rw [Category.assoc a (c.inv ≫ s) (e ≫ c.hom ≫ b),
    Category.assoc c.inv s (e ≫ c.hom ≫ b), ← Category.assoc s e (c.hom ≫ b),
    hh, Category.id_comp, Iso.inv_hom_id_assoc]

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The source extra degeneracy gives a simplicial homotopy from forward≫backward to the identity
of the source diagram in Over A. -/
def sourcePrism : SimplicialObject.Homotopy (overForward k σ d ≫ overBackward k σ d)
    (𝟙 (Over.lift (sourceResolution k σ d).left (sourceResolution k σ d).hom)) := by
  rw [forward_backward]
  exact (sourceOverExtra k σ d).homotopy

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The canonical right extra degeneracy gives a simplicial homotopy from the identity of the
target diagram to backward≫forward. -/
def targetPrism : SimplicialObject.Homotopy
    (𝟙 (Over.lift (canonicalResolution k σ).left (canonicalResolution k σ).hom))
    (overBackward k σ d ≫ overForward k σ d) := by
  rw [backward_forward]
  exact (targetOverExtra k σ).prism

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. Forget the forward slice map to obtain an augmented simplicial k-algebra map P→Q commuting
with augmentation to A. -/
def algebraForward : sourceResolution k σ d ⟶ canonicalResolution k σ :=
  Over.homMk
    (((SimplicialObject.whiskering (Over (algebra k σ)) (CommAlgCat.{max u v} k)).obj
      (Over.forget (algebra k σ))).map (overForward k σ d)) (by
        apply NatTrans.ext
        funext Δ
        exact ((overForward k σ d).app Δ).w)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. Forget the backward slice map to obtain an augmented simplicial k-algebra map Q→P commuting
with augmentation to A. -/
def algebraBackward : canonicalResolution k σ ⟶ sourceResolution k σ d :=
  Over.homMk
    (((SimplicialObject.whiskering (Over (algebra k σ)) (CommAlgCat.{max u v} k)).obj
      (Over.forget (algebra k σ))).map (overBackward k σ d)) (by
        apply NatTrans.ext
        funext Δ
        exact ((overBackward k σ d).app Δ).w)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The functor B→A ↦ A ⊗[B] Ω(B/k) sends the forward slice map to the corresponding simplicial
A-linear cotangent map. -/
def cotangentForward : cotangentSimplicial.{u, v} k (algebra k σ) (sourceResolution k σ d) ⟶
    cotangentSimplicial.{u, v} k (algebra k σ) (canonicalResolution k σ) :=
  ((SimplicialObject.whiskering (Over (algebra k σ)) (ModuleCat.{max u v} (algebra k σ))).obj
    (cotangentFunctor.{u, v} k (algebra k σ))).map (overForward k σ d)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The functor B→A ↦ A ⊗[B] Ω(B/k) sends the backward slice map to the corresponding simplicial
A-linear cotangent map. -/
def cotangentBackward : cotangentSimplicial.{u, v} k (algebra k σ) (canonicalResolution k σ) ⟶
    cotangentSimplicial.{u, v} k (algebra k σ) (sourceResolution k σ d) :=
  ((SimplicialObject.whiskering (Over (algebra k σ)) (ModuleCat.{max u v} (algebra k σ))).obj
    (cotangentFunctor.{u, v} k (algebra k σ))).map (overBackward k σ d)

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The forward cotangent map is the canonical cotangent simplicial map induced by the forward
augmented algebra comparison. -/
theorem cotangentForward_eq : cotangentForward k σ d =
    cotangentSimplicialMap.{u, v} k (algebra k σ) (algebraForward k σ d) := by
  apply NatTrans.ext
  funext Δ
  congr 1

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The backward cotangent map is the canonical cotangent simplicial map induced by the backward
augmented algebra comparison. -/
theorem cotangentBackward_eq : cotangentBackward k σ d =
    cotangentSimplicialMap.{u, v} k (algebra k σ) (algebraBackward k σ d) := by
  apply NatTrans.ext
  funext Δ
  congr 1

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. At each simplex Δ, the forward cotangent component is the cotangent-functor map of the
forward slice component PΔ→QΔ. -/
theorem cotangentForward_app (Δ : SimplexCategoryᵒᵖ) :
    (cotangentForward k σ d).app Δ =
      (cotangentFunctor.{u, v} k (algebra k σ)).map ((overForward k σ d).app Δ) := rfl

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. At each simplex Δ, the forward cotangent component sends a ⊗ dp to a ⊗ d(Fp), where a∈A, p∈PΔ
and F:PΔ→QΔ is the forward algebra component. -/
theorem cotangentForward_tensor (Δ : SimplexCategoryᵒᵖ) (a : algebra k σ)
    (p : (sourceResolution k σ d).left.obj Δ) :
    ((cotangentForward k σ d).app Δ).hom
      (cotangentTensor.{u, v} k (algebra k σ)
        ((Over.lift (sourceResolution k σ d).left (sourceResolution k σ d).hom).obj Δ) a p) =
    cotangentTensor.{u, v} k (algebra k σ)
      ((Over.lift (canonicalResolution k σ).left (canonicalResolution k σ).hom).obj Δ) a
      (((algebraForward k σ d).left.app Δ).hom p) := by
  rw [cotangentForward_app]
  exact cotangentMap_tensor.{u, v} k (algebra k σ) ((overForward k σ d).app Δ) a p

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. Normalize the cotangent simplicial modules by Moore chains. The forward and backward
normalized cotangent maps, with the transported source and target prisms, form a chain homotopy
equivalence. -/
def cotangentHomotopyEquiv :
    HomotopyEquiv
      ((normalizedMooreComplex (ModuleCat.{max u v} (algebra k σ))).obj
        (cotangentSimplicial.{u, v} k (algebra k σ) (sourceResolution k σ d)))
      (cotangentComplex k (algebra k σ)) where
  hom := (normalizedMooreComplex (ModuleCat.{max u v} (algebra k σ))).map (cotangentForward k σ d)
  inv := (normalizedMooreComplex (ModuleCat.{max u v} (algebra k σ))).map (cotangentBackward k σ d)
  homotopyHomInvId := by
    let F := (SimplicialObject.whiskering (Over (algebra k σ))
      (ModuleCat.{max u v} (algebra k σ))).obj (cotangentFunctor.{u, v} k (algebra k σ))
    let N := normalizedMooreComplex (ModuleCat.{max u v} (algebra k σ))
    let h := SimplicialObject.Homotopy.toNormalizedChainHomotopy
      ((sourcePrism k σ d).whiskerRight (cotangentFunctor.{u, v} k (algebra k σ)))
    have hcomp : N.map (F.map (overForward k σ d)) ≫ N.map (F.map (overBackward k σ d)) =
        N.map (F.map (overForward k σ d ≫ overBackward k σ d)) :=
      (N.map_comp _ _).symm.trans (congrArg N.map (F.map_comp _ _).symm)
    have hid : N.map (F.map (𝟙 (Over.lift (sourceResolution k σ d).left
        (sourceResolution k σ d).hom))) = 𝟙 _ :=
      (congrArg N.map (F.map_id _)).trans (N.map_id _)
    exact (_root_.Homotopy.ofEq hcomp).trans (h.trans (_root_.Homotopy.ofEq hid))
  homotopyInvHomId := by
    let F := (SimplicialObject.whiskering (Over (algebra k σ))
      (ModuleCat.{max u v} (algebra k σ))).obj (cotangentFunctor.{u, v} k (algebra k σ))
    let N := normalizedMooreComplex (ModuleCat.{max u v} (algebra k σ))
    let h := (SimplicialObject.Homotopy.toNormalizedChainHomotopy
      ((targetPrism k σ d).whiskerRight (cotangentFunctor.{u, v} k (algebra k σ)))).symm
    have hcomp : N.map (F.map (overBackward k σ d)) ≫ N.map (F.map (overForward k σ d)) =
        N.map (F.map (overBackward k σ d ≫ overForward k σ d)) :=
      (N.map_comp _ _).symm.trans (congrArg N.map (F.map_comp _ _).symm)
    have hid : N.map (F.map (𝟙 (Over.lift (canonicalResolution k σ).left
        (canonicalResolution k σ).hom))) = 𝟙 _ :=
      (congrArg N.map (F.map_id _)).trans (N.map_id _)
    exact (_root_.Homotopy.ofEq hcomp).trans (h.trans (_root_.Homotopy.ofEq hid))

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. The forward map of the normalized cotangent homotopy equivalence is the normalized cotangent
map of the forward augmented algebra comparison. -/
theorem cotangentHomotopyEquiv_hom : (cotangentHomotopyEquiv k σ d).hom =
    (normalizedMooreComplex (ModuleCat.{max u v} (algebra k σ))).map
      (cotangentSimplicialMap.{u, v} k (algebra k σ) (algebraForward k σ d)) := by
  change (normalizedMooreComplex _).map (cotangentForward k σ d) = _
  rw [cotangentForward_eq]

/-- Let k be a commutative ring, σ a variable set, d∈ℕ and A=k[σ]. Let P be the free-algebra image
of the variable-wise augmented standard d-simplex, and Q the canonical polynomial resolution of
A. For any A-module M in independent carrier universe t, the additive functor M ⊗[A] − sends the
normalized cotangent homotopy equivalence to the coefficient homotopy equivalence. Its tensor
carrier is max(t,u,v). -/
def coefficientHomotopyEquiv (M : ModuleCat.{t} (algebra k σ)) :
    HomotopyEquiv
      ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} (algebra k σ)).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj ((normalizedMooreComplex (ModuleCat.{max u v} (algebra k σ))).obj
          (cotangentSimplicial.{u, v} k (algebra k σ) (sourceResolution k σ d))))
      ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} (algebra k σ)).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cotangentComplex k (algebra k σ))) :=
  ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} (algebra k σ)).obj M).mapHomotopyEquiv
    (cotangentHomotopyEquiv k σ d)

end CommAlgCat.StandardSimplexPolynomialCotangent

end
