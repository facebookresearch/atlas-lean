/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentHorizontal
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentDerived
public import MathlibExt.AlgebraicTopology.DoldKan.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Cotangent comparison for polynomial simplicial resolutions

Let `Q → const A` be an augmented simplicial commutative `k`-algebra. Its double
polynomial cotangent replacement gives a span from the normalized diagonal complex
to the normalized cotangent model of `Q` and to the canonical cotangent complex of `A`.
Degreewise polynomial presentations make the first map a quasi-isomorphism; the
trivial-fibration condition on the underlying augmentation makes the second one a
quasi-isomorphism.

Polynomial differentials and the normalization retraction give projective terms, so
the two maps belong to chain homotopy equivalences under their respective hypotheses.
Together they compare the cotangent models of polynomial resolutions. Extending chain
degree `n` to cochain degree `-n` and localizing gives the corresponding derived
isomorphisms. The ground-ring, module-carrier, and derived-category universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v w

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The normalized Moore complex of the degreewise cotangent diagram of an augmented
simplicial algebra `Q → const A`.
-/
def cotangentResolutionComplex
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    ChainComplex (ModuleCat.{max u v} A) ℕ :=
  (normalizedMooreComplex (ModuleCat.{max u v} A)).obj (cotangentSimplicial k A Q)

/--
The normalized Moore complex of the diagonal of the bisimplicial polynomial
cotangent replacement of `Q`.
-/
def polynomialCotangentReplacementComplex
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    ChainComplex (ModuleCat.{max u v} A) ℕ :=
  (normalizedMooreComplex (ModuleCat.{max u v} A)).obj
    ((SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).obj
      (polynomialCotangentReplacement k A Q))

/--
The chain map from the normalized diagonal replacement to the normalized cotangent
model of `Q`, induced by the vertical augmentation.
-/
def polynomialCotangentReplacementChainToOriginal
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    polynomialCotangentReplacementComplex k A Q ⟶ cotangentResolutionComplex k A Q :=
  (normalizedMooreComplex (ModuleCat.{max u v} A)).map
    (polynomialCotangentReplacementToOriginal k A Q)

/--
The chain map from the normalized diagonal replacement to the canonical cotangent
complex of `A`, induced by the horizontal augmentation.
-/
def polynomialCotangentReplacementChainToStandard
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    polynomialCotangentReplacementComplex k A Q ⟶ cotangentComplex k A :=
  (normalizedMooreComplex (ModuleCat.{max u v} A)).map
    (polynomialCotangentReplacementToStandard k A Q)

/--
If every simplicial degree of `Q` admits a polynomial presentation, the vertical
comparison from its normalized polynomial replacement is a quasi-isomorphism.
-/
theorem polynomialCotangentReplacementChainToOriginal_quasiIso
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hpoly : ∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋q⦌))) :
    QuasiIso (polynomialCotangentReplacementChainToOriginal k A Q) :=
  SimplicialObject.quasiIso_normalizedMap_of_alternatingMap
    (polynomialCotangentReplacementToOriginal k A Q)
    (polynomialCotangentReplacementToOriginal_quasiIso k A Q hpoly)

/--
If the underlying augmentation of `Q` is a trivial fibration, the normalized horizontal
comparison to the canonical cotangent complex is a quasi-isomorphism.
-/
theorem polynomialCotangentReplacementChainToStandard_quasiIso
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hQ : polynomialCotangentResolutionCondition k A Q) :
    QuasiIso (polynomialCotangentReplacementChainToStandard k A Q) :=
  SimplicialObject.quasiIso_normalizedMap_of_alternatingMap
    (polynomialCotangentReplacementToStandard k A Q)
    (polynomialCotangentReplacementToStandard_quasiIso k A Q hQ)

/--
A polynomial presentation of `Q_n` makes the degree-`n` cotangent module
`A ⊗[Q_n] Ω(Q_n/k)` projective as an `A`-module.
-/
theorem cotangentResolutionDegree_projective
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ)
    (hpoly : ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋n⦌))) :
    Projective ((cotangentSimplicial k A Q).obj (op ⦋n⦌)) := by
  obtain ⟨σ, ⟨e⟩⟩ := hpoly
  exact polynomialCotangent_projective k A (Over.mk (Q.hom.app (op ⦋n⦌))) σ e

/--
If `Q_n` admits a polynomial presentation, the degree-`n` term of its normalized
cotangent complex is projective, as a retract of the corresponding cotangent module.
-/
theorem cotangentResolutionComplex_term_projective
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ)
    (hpoly : ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋n⦌))) :
    Projective ((cotangentResolutionComplex k A Q).X n) := by
  letI : Projective ((cotangentSimplicial k A Q).obj (op ⦋n⦌)) :=
    cotangentResolutionDegree_projective k A Q n hpoly
  exact SimplicialObject.normalizedDegree_projective (cotangentSimplicial k A Q) n

/--
Every degree of the diagonal polynomial cotangent replacement is projective as an
`A`-module, for any augmented simplicial algebra `Q`.
-/
theorem polynomialCotangentReplacementDegree_projective
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ) :
    Projective (((SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).obj
      (polynomialCotangentReplacement k A Q)).obj (op ⦋n⦌)) :=
  polynomialCotangentDegree_projective k A ((Over.lift Q.left Q.hom).obj (op ⦋n⦌)) n

/--
Every term of the normalized polynomial cotangent replacement complex is projective,
as a retract of its degreewise polynomial cotangent module.
-/
theorem polynomialCotangentReplacementComplex_term_projective
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ) :
    Projective ((polynomialCotangentReplacementComplex k A Q).X n) := by
  let X := (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).obj
    (polynomialCotangentReplacement k A Q)
  letI : Projective (X.obj (op ⦋n⦌)) := polynomialCotangentReplacementDegree_projective k A Q n
  exact SimplicialObject.normalizedDegree_projective X n

/--
Under degreewise polynomial presentations of `Q`, there is a chain homotopy
equivalence from the replacement complex to its cotangent model whose forward map
is the vertical normalized comparison.
-/
theorem polynomialCotangentReplacementToOriginal_existsHomotopyEquiv
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hpoly : ∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋q⦌))) :
    ∃ e : HomotopyEquiv (polynomialCotangentReplacementComplex k A Q)
        (cotangentResolutionComplex k A Q),
      e.hom = polynomialCotangentReplacementChainToOriginal k A Q := by
  letI : ∀ n, Projective ((polynomialCotangentReplacementComplex k A Q).X n) :=
    fun n => polynomialCotangentReplacementComplex_term_projective k A Q n
  letI : ∀ n, Projective ((cotangentResolutionComplex k A Q).X n) :=
    fun n => cotangentResolutionComplex_term_projective k A Q n (hpoly n)
  exact (ChainComplex.quasiIso_iff_of_projective _).mp
    (polynomialCotangentReplacementChainToOriginal_quasiIso k A Q hpoly)

/--
Under the underlying trivial-fibration condition on `Q`, there is a chain homotopy
equivalence from the replacement complex to the canonical cotangent complex whose
forward map is the horizontal normalized comparison.
-/
theorem polynomialCotangentReplacementToStandard_existsHomotopyEquiv
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hQ : polynomialCotangentResolutionCondition k A Q) :
    ∃ e : HomotopyEquiv (polynomialCotangentReplacementComplex k A Q) (cotangentComplex k A),
      e.hom = polynomialCotangentReplacementChainToStandard k A Q := by
  letI : ∀ n, Projective ((polynomialCotangentReplacementComplex k A Q).X n) :=
    fun n => polynomialCotangentReplacementComplex_term_projective k A Q n
  letI : ∀ n, Projective ((cotangentComplex k A).X n) := cotangentComplex_term_projective k A
  exact (ChainComplex.quasiIso_iff_of_projective _).mp
    (polynomialCotangentReplacementChainToStandard_quasiIso k A Q hQ)

/--
The chain homotopy equivalence from the normalized cotangent model of `Q` to the
canonical cotangent complex, using degreewise polynomial presentations and the
underlying trivial-fibration condition through the two replacement comparisons.
-/
def cotangentResolutionHomotopyEquiv
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hpoly : ∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋q⦌)))
    (hQ : polynomialCotangentResolutionCondition k A Q) :
    HomotopyEquiv (cotangentResolutionComplex k A Q) (cotangentComplex k A) :=
  (Classical.choose (polynomialCotangentReplacementToOriginal_existsHomotopyEquiv k A Q hpoly)).symm.trans
      (Classical.choose (polynomialCotangentReplacementToStandard_existsHomotopyEquiv k A Q hQ))

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]

/--
Fix a derived category of `ModuleCat.{max u v} A` in universe `w`
(`HasDerivedCategory.{w}`).

The derived-category object obtained from the normalized cotangent model of `Q` by
placing chain degree `n` in cochain degree `-n`, extending by zero in positive cochain
degrees, and applying derived localization.
-/
def cotangentResolutionDerived
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    DerivedCategory (ModuleCat.{max u v} A) :=
  DerivedCategory.Q.obj ((cotangentResolutionComplex k A Q).extend ComplexShape.embeddingDownNat)

/--
Fix a derived category of `ModuleCat.{max u v} A` in universe `w`
(`HasDerivedCategory.{w}`).

For a degreewise polynomial augmented algebra satisfying the underlying
trivial-fibration condition, the isomorphism from its derived cotangent object to the
canonical derived cotangent object of `A`, induced by the replacement span.
-/
def cotangentResolutionDerivedIso
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hpoly : ∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋q⦌)))
    (hQ : polynomialCotangentResolutionCondition k A Q) :
    cotangentResolutionDerived k A Q ≅ cotangentDerived k A := by
  let v := HomologicalComplex.extendMap
    (polynomialCotangentReplacementChainToOriginal k A Q) ComplexShape.embeddingDownNat
  let h := HomologicalComplex.extendMap
    (polynomialCotangentReplacementChainToStandard k A Q) ComplexShape.embeddingDownNat
  letI : QuasiIso (polynomialCotangentReplacementChainToOriginal k A Q) :=
    polynomialCotangentReplacementChainToOriginal_quasiIso k A Q hpoly
  letI : QuasiIso (polynomialCotangentReplacementChainToStandard k A Q) :=
    polynomialCotangentReplacementChainToStandard_quasiIso k A Q hQ
  letI : QuasiIso v := inferInstance
  letI : QuasiIso h := inferInstance
  letI : IsIso (DerivedCategory.Q.map v) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) v).mpr inferInstance
  have hv : IsIso (DerivedCategory.Q.map v) := inferInstance
  have hh : IsIso (DerivedCategory.Q.map h) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) h).mpr inferInstance
  exact (@asIso _ _ _ _ (DerivedCategory.Q.map v) hv).symm ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map h) hh

/--
Fix a derived category of `ModuleCat.{max u v} A` in universe `w`
(`HasDerivedCategory.{w}`).

The derived isomorphism between the cotangent objects of two augmented diagrams,
each with degreewise polynomial presentations and an underlying trivial-fibration
augmentation, obtained by comparison with the canonical object.
-/
def cotangentResolutionsDerivedIso
    (Q Q' : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hpoly : ∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋q⦌)))
    (hpoly' : ∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q'.left.obj (op ⦋q⦌)))
    (hQ : polynomialCotangentResolutionCondition k A Q)
    (hQ' : polynomialCotangentResolutionCondition k A Q') :
    cotangentResolutionDerived k A Q ≅ cotangentResolutionDerived k A Q' :=
  cotangentResolutionDerivedIso k A Q hpoly hQ ≪≫
    (cotangentResolutionDerivedIso k A Q' hpoly' hQ').symm

end CommAlgCat

end
