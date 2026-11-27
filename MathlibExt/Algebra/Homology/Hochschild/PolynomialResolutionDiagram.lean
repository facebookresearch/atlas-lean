/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.AugmentedFormLevel
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDifferentialFormAlgebraNaturality
public import MathlibExt.Algebra.Category.CommAlgCat.CanonicalPolynomialResolutionComparison
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.Simplicial
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPage
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex

/-!
# Hochschild bicomplex of the canonical polynomial resolution

Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. The canonical
augmented simplicial polynomial resolution `P` of `B` gives a simplicial diagram of Hochschild
chain complexes with coefficient `B`. Its term at simplicial degree `p` and Hochschild degree
`q` is `B ⊗_k P_p^{⊗ q}`. Applying the alternating-face complex in the simplicial direction
gives a first-quadrant bicomplex, its signed direct-sum total, and its horizontal-filtration
spectral sequence.

Each polynomial level has an integral HKR isomorphism from Hochschild homology to `B ⊗_{P_p}
Λ^q Ω¹_{P_p/k}`. Naturality for maps over `B` assembles these comparisons into a simplicial
higher-form diagram. Page one consists of those form modules, and page two is the homology of
their alternating-face complex.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v

namespace ModuleCat.Algebra.Hochschild.AndreQuillenResolution

open _root_.ModuleCat.Algebra.Hochschild.Symmetric
open Symmetric.AugmentedAlgebra
open PolynomialDiagonal

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)


/-- For a commutative ring `k : Type u` and `B : CommAlgCat.{max u v} k`, `resolution k B` is
`CanonicalPolynomialResolutionComparison.canonical k B`, the augmented simplicial polynomial
resolution of `B`. Its level `p` is the `(p+1)`-fold polynomial free-forget construction on
`B`. -/
abbrev resolution := CommAlgCat.CanonicalPolynomialResolutionComparison.canonical k B

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. The simplicial
diagram `algebraDiagram k B : SimplicialObject (Over B)` sends each level of `resolution k B`
to that algebra equipped with its augmentation to `B`. Its operators are the resolution
algebra maps commuting with these augmentations. -/
abbrev algebraDiagram : SimplicialObject (Over B) :=
  Over.lift (resolution k B).left (resolution k B).hom

/-- For a commutative ring `k : Type u` and `B : CommAlgCat.{max u v} k`, the simplicial object
`diagram k B` takes values in `ChainComplex (ModuleCat.{max u v} k) ℕ`. At level `P_p` of
`resolution k B`, it is the Hochschild chain complex of `P_p/k` with coefficient `B`, using
the augmentation action of `P_p` on `B`. -/
def diagram : SimplicialObject (ChainComplex (ModuleCat.{max u v} k) ℕ) :=
  Symmetric.AugmentedAlgebra.simplicialDiagram k B (resolution k B)

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. The map
`diagramAugmentation k B` goes from `diagram k B` to the constant simplicial chain complex
`Symmetric.AugmentedAlgebra.regularComplex k B`. In Hochschild degree `q`, it retains the
first coefficient in `B` and applies the resolution augmentation to each of the `q` tail
factors. -/
def diagramAugmentation : diagram k B ⟶
    (SimplicialObject.const (ChainComplex (ModuleCat.{max u v} k) ℕ)).obj
      (Symmetric.AugmentedAlgebra.regularComplex k B) :=
  Symmetric.AugmentedAlgebra.simplicialAugmentation k B (resolution k B)

/-- For a commutative ring `k : Type u` and `B : CommAlgCat.{max u v} k`, applying the alternating-face complex to
`diagram k B` gives
`bicomplex k B : HomologicalComplex₂ (ModuleCat.{max u v} k) (.down ℕ) (.down ℕ)`.
Its `(p,q)` term is `B ⊗_k P_p^{⊗ q}`; the first differential is the alternating sum of resolution faces and the second
is the Hochschild boundary. -/
def bicomplex : HomologicalComplex₂ (ModuleCat.{max u v} k) (.down ℕ) (.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v} k) ℕ)).obj (diagram k B)

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. The chain complex
`totalComplex k B` is `(bicomplex k B).total (.down ℕ)`. In total degree `n`, it is the direct
sum of the `(p,q)` terms with `p+q=n`, with the signs prescribed by the down-`ℕ` totalization
of the commuting bicomplex. -/
abbrev totalComplex : ChainComplex (ModuleCat.{max u v} k) ℕ := (bicomplex k B).total (.down ℕ)

/-- For a commutative ring `k : Type u` and `B : CommAlgCat.{max u v} k`, `spectralSequence k B`
is the horizontal first-quadrant spectral sequence of `bicomplex k B`. It uses the complete
horizontal filtration of the signed total of the polynomial-resolution Hochschild bicomplex,
with indices `(p,q) ∈ ℕ × ℕ`. -/
abbrev spectralSequence := HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence (bicomplex k B)

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `θ : i ⟶ j` in `SimplexCategoryᵒᵖ`. For `q
: ℕ`, `b : B`, and `a : Fin q → (resolution k B).left.obj i`,
`(((diagram k B).map θ).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) = b ⊗ₜ[k] PiTensorProduct.tprod k (fun r =>
((resolution k B).left.map θ).hom (a r))`.
The coefficient is retained and the algebra operator acts on every tail factor. -/
theorem diagram_map_tprod {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j)
    (q : ℕ) (b : B) (a : Fin q → (resolution k B).left.obj i) :
    (((diagram k B).map θ).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
      b ⊗ₜ[k] PiTensorProduct.tprod k (fun r => ((resolution k B).left.map θ).hom (a r)) :=
  Symmetric.AugmentedAlgebra.simplicialDiagram_map_tprod k B (resolution k B) θ q b a

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `p : ℕ`, the generator
type `«variables» k B p : Type (max u v)` is the underlying carrier of
`(CommAlgCat.polynomialPower k p).obj B`. The degree-`p` resolution algebra is presented as
polynomials over `k` in this type of generators. -/
abbrev «variables» (p : ℕ) : Type (max u v) := (CommAlgCat.polynomialPower k p).obj B

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `p : ℕ`. Write `e_p
= polynomialResolutionObjIso k B p` and `ε_p = (resolution k B).hom.app (op ⦋p⦌)`. The object
`polynomialLevel k B p : Over B` is the polynomial algebra in `«variables» k B p` with
augmentation `e_p.inv ≫ ε_p` to `B`. -/
def polynomialLevel (p : ℕ) : Over B :=
  Over.mk ((CommAlgCat.polynomialResolutionObjIso k B p).inv ≫
    (resolution k B).hom.app (op ⦋p⦌))

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `p : ℕ`, there is an isomorphism in `Over B`
`(algebraDiagram k B).obj (op ⦋p⦌) ≅ polynomialLevel k B p`.
Its underlying algebra isomorphism is `polynomialResolutionObjIso k B p`; the presented level's augmentation is
transported by its inverse. -/
def polynomialLevelIso (p : ℕ) :
    (algebraDiagram k B).obj (op ⦋p⦌) ≅ polynomialLevel k B p :=
  Over.isoMk (CommAlgCat.polynomialResolutionObjIso k B p) (by
    let e := CommAlgCat.polynomialResolutionObjIso k B p
    let ε := (resolution k B).hom.app (op ⦋p⦌)
    change e.hom ≫ (e.inv ≫ ε) = ε
    exact (Category.assoc e.hom e.inv ε).symm.trans
      ((congrArg (fun t => t ≫ ε) e.hom_inv_id).trans (Category.id_comp ε)))

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`,
`homologyOverFunctor k B q : Over B ⥤ ModuleCat.{max u v} k` sends an augmented commutative
algebra `R ⟶ B` to `HH_q(R/k;B)`. The coefficient action is through that augmentation; a map
over `B` acts by its induced Hochschild chain map and degree-`q` homology map. -/
def homologyOverFunctor (q : ℕ) : Over B ⥤ (ModuleCat.{max u v} k) :=
  Symmetric.AugmentedAlgebra.functor k B ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k) (.down ℕ) q

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `p, q : ℕ`. For the presented polynomial
algebra `R_p = polynomialLevel k B p` over `B`, integral polynomial HKR gives
`(homologyOverFunctor k B q).obj R_p ≅ (higherGroundFunctor k B q).obj R_p`.
The source is `HH_q(R_p/k;B)` and the target is the underlying `k`-module of `B ⊗_{R_p} Λ^q_{R_p} Ω¹_{R_p/k}`. -/
def polynomialLevelHKR (p q : ℕ) :
    (homologyOverFunctor k B q).obj (polynomialLevel k B p) ≅
      (higherGroundFunctor k B q).obj (polynomialLevel k B p) := by
  let P := polynomialLevel k B p
  let V := «variables» k B p
  let PS := MvPolynomial V k
  let ε : PS →ₐ[k] B :=
    ((CommAlgCat.polynomialResolutionObjIso k B p).inv ≫
      (resolution k B).hom.app (op ⦋p⦌)).hom
  letI : Algebra PS B := ε.toRingHom.toAlgebra
  letI : Module PS B := inferInstance
  letI : IsScalarTower k PS B := IsScalarTower.of_algHom ε
  let X : ModuleCat.{max u v} k := (homologyOverFunctor k B q).obj P
  let Y : ModuleCat.{max u v} k := (Symmetric.coefficientDifferentialFormComplex k PS B).X q
  let Z : ModuleCat.{max u v} k := (higherGroundFunctor k B q).obj P
  let e : X ≅ Y := polynomialDifferentialFormHomologyIso.{u, max u v, max u v} k V B q
  let t : Y ≅ Z := rawFormLevelIso.{u, v} k B q P
  exact e ≪≫ t

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, `p, p', q : ℕ`, and an algebra map `f :
polynomialLevel k B p ⟶ polynomialLevel k B p'` over `B`,
`(homologyOverFunctor k B q).map f ≫ (polynomialLevelHKR k B p' q).hom = (polynomialLevelHKR k B p q).hom ≫
(higherGroundFunctor k B q).map f`.
The square compares the induced Hochschild-homology and higher-form maps for every such augmented algebra map. -/
@[reassoc]
theorem polynomialLevelHKR_naturality {p p' : ℕ}
    (f : polynomialLevel k B p ⟶ polynomialLevel k B p') (q : ℕ) :
    (homologyOverFunctor k B q).map f ≫ (polynomialLevelHKR k B p' q).hom =
      (polynomialLevelHKR k B p q).hom ≫ (higherGroundFunctor k B q).map f := by
  let P := polynomialLevel k B p
  let Q := polynomialLevel k B p'
  let PS := MvPolynomial («variables» k B p) k
  let PT := MvPolynomial («variables» k B p') k
  let εS : PS →ₐ[k] B := P.hom.hom
  let εT : PT →ₐ[k] B := Q.hom.hom
  letI : Algebra PS B := CommAlgCat.cotangentAlgebra k B P
  letI : Algebra PT B := CommAlgCat.cotangentAlgebra k B Q
  letI : Module PS B := inferInstance
  letI : Module PT B := inferInstance
  letI : IsScalarTower k PS B := CommAlgCat.cotangentScalarTower k B P
  letI : IsScalarTower k PT B := CommAlgCat.cotangentScalarTower k B Q
  let g : PS →ₐ[k] PT := f.left.hom
  have hcoef : ∀ (a : PS) (b : B), (LinearMap.id : B →ₗ[k] B) (a • b) =
      g a • (LinearMap.id : B →ₗ[k] B) b := coefficientCompatibility k B f
  have hH := polynomialDifferentialFormHomologyIso_algebra.{u, max u v, max u v} k g
    (LinearMap.id : B →ₗ[k] B) hcoef q
  have hF := rawFormLevelIso_naturality k B f q
  have hAlgS : (CommAlgCat.cotangentAlgebra k B P : Algebra PS B) =
      εS.toRingHom.toAlgebra := rfl
  have hAlgT : (CommAlgCat.cotangentAlgebra k B Q : Algebra PT B) =
      εT.toRingHom.toAlgebra := rfl
  let H := homologyOverFunctor k B q
  let G := higherGroundFunctor k B q
  let eS : H.obj P ≅ rawFormLevel k B q P :=
    polynomialDifferentialFormHomologyIso.{u, max u v, max u v} k («variables» k B p) B q
  let eT : H.obj Q ≅ rawFormLevel k B q Q :=
    polynomialDifferentialFormHomologyIso.{u, max u v, max u v} k («variables» k B p') B q
  let tS : rawFormLevel k B q P ≅ G.obj P := rawFormLevelIso.{u, v} k B q P
  let tT : rawFormLevel k B q Q ≅ G.obj Q := rawFormLevelIso.{u, v} k B q Q
  let F : rawFormLevel k B q P ⟶ rawFormLevel k B q Q := rawFormMap k B f q
  let h : H.obj P ⟶ H.obj Q := H.map f
  let t : G.obj P ⟶ G.obj Q := G.map f
  have hH0 : h ≫ eT.hom = eS.hom ≫ F := hH
  have hF0 : F ≫ tT.hom = tS.hom ≫ t := hF
  have heS : (polynomialLevelHKR k B p q).hom = eS.hom ≫ tS.hom := rfl
  have heT : (polynomialLevelHKR k B p' q).hom = eT.hom ≫ tT.hom := rfl
  have h1 : h ≫ (polynomialLevelHKR k B p' q).hom = h ≫ (eT.hom ≫ tT.hom) :=
    congrArg (fun c : H.obj Q ⟶ G.obj Q => h ≫ c) heT
  have h2 : h ≫ (eT.hom ≫ tT.hom) = (eS.hom ≫ F) ≫ tT.hom :=
    (Category.assoc h eT.hom tT.hom).symm.trans
      (congrArg (fun c : H.obj P ⟶ rawFormLevel k B q Q => c ≫ tT.hom) hH0)
  have h3 : (eS.hom ≫ F) ≫ tT.hom = eS.hom ≫ (tS.hom ≫ t) :=
    (Category.assoc eS.hom F tT.hom).trans
      (congrArg (fun c : rawFormLevel k B q P ⟶ G.obj Q => eS.hom ≫ c) hF0)
  have h4 : eS.hom ≫ (tS.hom ≫ t) = (polynomialLevelHKR k B p q).hom ≫ t :=
    (Category.assoc eS.hom tS.hom t).symm.trans
      (congrArg (fun c : H.obj P ⟶ G.obj P => c ≫ t) heS.symm)
  exact h1.trans (h2.trans (h3.trans h4))

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `p, q : ℕ`, the isomorphism
`((diagram k B).obj (op ⦋p⦌)).homology q ≅ (higherGroundFunctor k B q).obj ((algebraDiagram k B).obj (op ⦋p⦌))`
identifies the level-`p` Hochschild homology with coefficient higher forms. It transports polynomial HKR through
`polynomialLevelIso k B p`, so the comparison is on the canonical resolution level itself. -/
def columnHKR (p q : ℕ) :
    ((diagram k B).obj (op ⦋p⦌)).homology q ≅
      (higherGroundFunctor k B q).obj ((algebraDiagram k B).obj (op ⦋p⦌)) :=
  (homologyOverFunctor k B q).mapIso (polynomialLevelIso k B p) ≪≫
    polynomialLevelHKR k B p q ≪≫
      ((higherGroundFunctor k B q).mapIso (polynomialLevelIso k B p)).symm

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `θ : op ⦋p⦌ ⟶ op ⦋p'⦌` a simplicial
operator. For `q : ℕ`,
`HomologicalComplex.homologyMap ((diagram k B).map θ) q ≫ (columnHKR k B p' q).hom = (columnHKR k B p q).hom ≫
(higherGroundFunctor k B q).map ((algebraDiagram k B).map θ)`.
The equation includes faces, degeneracies, and their composites. -/
@[reassoc]
theorem columnHKR_naturality {p p' : ℕ} (θ : op ⦋p⦌ ⟶ op ⦋p'⦌) (q : ℕ) :
    HomologicalComplex.homologyMap ((diagram k B).map θ) q ≫ (columnHKR k B p' q).hom =
      (columnHKR k B p q).hom ≫ (higherGroundFunctor k B q).map ((algebraDiagram k B).map θ) := by
  let H := homologyOverFunctor k B q
  let G := higherGroundFunctor k B q
  let eS := polynomialLevelIso k B p
  let eT := polynomialLevelIso k B p'
  let f := (algebraDiagram k B).map θ
  let f' := eS.inv ≫ f ≫ eT.hom
  let hS := H.mapIso eS
  let hT := H.mapIso eT
  let gS := G.mapIso eS
  let gT := G.mapIso eT
  have h := polynomialLevelHKR_naturality k B f' q
  rw [show H.map f' = hS.inv ≫ H.map f ≫ hT.hom by
    simp only [f', hS, hT, Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv]] at h
  rw [show G.map f' = gS.inv ≫ G.map f ≫ gT.hom by
    simp only [f', gS, gT, Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv]] at h
  have h' := congrArg (fun t => hS.hom ≫ t ≫ gT.inv) h
  have hn : H.map f ≫ (hT.hom ≫ ((polynomialLevelHKR k B p' q).hom ≫ gT.inv)) =
      (hS.hom ≫ ((polynomialLevelHKR k B p q).hom ≫ gS.inv)) ≫ G.map f := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h'
  have hMap : H.map f = HomologicalComplex.homologyMap ((diagram k B).map θ) q := rfl
  have hSource : (columnHKR k B p q).hom =
      hS.hom ≫ ((polynomialLevelHKR k B p q).hom ≫ gS.inv) := rfl
  have hTarget : (columnHKR k B p' q).hom =
      hT.hom ≫ ((polynomialLevelHKR k B p' q).hom ≫ gT.inv) := rfl
  have h1 : HomologicalComplex.homologyMap ((diagram k B).map θ) q ≫
        (columnHKR k B p' q).hom = H.map f ≫ (columnHKR k B p' q).hom :=
    congrArg (fun a : H.obj ((algebraDiagram k B).obj (op ⦋p⦌)) ⟶
      H.obj ((algebraDiagram k B).obj (op ⦋p'⦌)) => a ≫ (columnHKR k B p' q).hom) hMap.symm
  have h2 : H.map f ≫ (columnHKR k B p' q).hom =
      H.map f ≫ (hT.hom ≫ ((polynomialLevelHKR k B p' q).hom ≫ gT.inv)) :=
    congrArg (fun a : H.obj ((algebraDiagram k B).obj (op ⦋p'⦌)) ⟶
      G.obj ((algebraDiagram k B).obj (op ⦋p'⦌)) => H.map f ≫ a) hTarget
  have h3 : (hS.hom ≫ ((polynomialLevelHKR k B p q).hom ≫ gS.inv)) ≫ G.map f =
      (columnHKR k B p q).hom ≫ G.map f :=
    congrArg (fun a : H.obj ((algebraDiagram k B).obj (op ⦋p⦌)) ⟶
      G.obj ((algebraDiagram k B).obj (op ⦋p⦌)) => a ≫ G.map f) hSource.symm
  exact h1.trans (h2.trans (hn.trans h3))

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, the simplicial
`k`-module `formDiagram k B q` is `(algebraDiagram k B) ⋙ higherGroundFunctor k B q`. At a
resolution level `P_i`, it is the underlying `k`-module of `B ⊗_{P_i} Λ^q_{P_i} Ω¹_{P_i/k}`,
with operators induced by the augmented algebra maps. -/
def formDiagram (q : ℕ) : SimplicialObject (ModuleCat.{max u v} k) :=
  (algebraDiagram k B) ⋙ higherGroundFunctor k B q

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `q : ℕ`. Taking Hochschild homology in
degree `q` levelwise gives an isomorphism of simplicial `k`-modules
`diagram k B ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k) (.down ℕ) q ≅ formDiagram k B q`.
Its components are `columnHKR k B p q`, and their algebra-map naturality supplies the simplicial coherence. -/
def verticalHomologyDiagramIso (q : ℕ) :
    diagram k B ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k) (.down ℕ) q ≅ formDiagram k B q :=
  NatIso.ofComponents (fun i => columnHKR k B i.unop.len q) (by
    intro i j θ
    exact columnHKR_naturality k B θ q)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, there is an isomorphism of
nonnegative chain complexes
`(bicomplex k B).verticalHomologyComplex q ≅ (alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (formDiagram k B
q)`.
It identifies the horizontal differential on degree-`q` Hochschild homology with the alternating resolution-face
differential on coefficient higher forms. -/
def verticalHomologyFormComplexIso (q : ℕ) :
    (bicomplex k B).verticalHomologyComplex q ≅
      (alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (formDiagram k B q) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k) (.down ℕ) q)).app (diagram k B) ≪≫
      (alternatingFaceMapComplex (ModuleCat.{max u v} k)).mapIso (verticalHomologyDiagramIso k B q)

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. For `p, q : ℕ`,
`((spectralSequence k B).page 1).X (p,q) ≅ (higherGroundFunctor k B q).obj ((algebraDiagram k B).obj (op ⦋p⦌))`.
The target is the `k`-module underlying `B ⊗_{P_p} Λ^q Ω¹_{P_p/k}` for the canonical polynomial-resolution level `P_p`.
-/
def firstPageIso (p q : ℕ) :
    ((spectralSequence k B).page 1).X (p, q) ≅
      (higherGroundFunctor k B q).obj ((algebraDiagram k B).obj (op ⦋p⦌)) :=
  HomologicalComplex₂.horizontalFirstPageNormalizedVerticalHomologyIso (bicomplex k B) p q ≪≫
    columnHKR k B p q

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `p, q : ℕ`,
`((spectralSequence k B).page 2).X (p,q) ≅ ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (formDiagram k B
q)).homology p`.
The second page is the degree-`p` homology, in the resolution direction, of the simplicial degreewise `q`-form diagram.
-/
def secondPageFormHomologyIso (p q : ℕ) :
    ((spectralSequence k B).page 2).X (p, q) ≅
      ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (formDiagram k B q)).homology p :=
  HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso (bicomplex k B) p q ≪≫
    HomologicalComplex.homologyMapIso (verticalHomologyFormComplexIso k B q) p

end ModuleCat.Algebra.Hochschild.AndreQuillenResolution
