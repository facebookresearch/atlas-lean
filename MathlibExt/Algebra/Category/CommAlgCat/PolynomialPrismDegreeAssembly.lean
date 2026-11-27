/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialPrismNondegenerateDegreeExtension
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialPrismDegreeOne
public import MathlibExt.AlgebraicTopology.SimplicialObject.SplittingPrismFaceDescent

/-!
# Successive degrees of a compatible polynomial prism

Let `P → const A` and `Q → const A` be augmented simplicial commutative `k`-algebras,
let `P` have a compatible polynomial splitting, and let `f, g : P ⟶ Q` be augmented maps.
A prefix supplies primitive maps on every nondegenerate summand and the resulting
whole-source prism maps, with endpoint, face, and augmentation laws through a bounded
source degree. The zero endpoint faces are oriented by `d₀ H₀⁰ = g₀` and `d₁ H₀⁰ = f₀`.

Under additive asphericity of `Q`, the zero-degree edge and the two degree-one maps
produce a prefix through degree one. A prefix through degree `d + 1` extends through
`d + 2` by filling the polynomial shell on the new nondegenerate summand and descending
along the splitting. Every primitive prescription and whole-source operator in degrees
`m < d + 2` remains unchanged. The primitive family is defined in all degrees, while face and augmentation
laws are required only through the stated bound.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open CategoryTheory.SimplicialObject.SplittingPrismFaceDescent
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialPrismDegreeAssembly

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (f g : P ⟶ Q)

/--
A total primitive family on the nondegenerate summands of `P`, with zero-degree
endpoint faces, relative prism face equations for each degree pair `d, d + 1` with
`d + 1 ≤ n`, and augmentation equations in all source degrees `m ≤ n`.
-/
structure Prefix (n : ℕ) where
  /--
  For every source degree `m` and vertex `i : Fin (m + 1)`, a map from the
  nondegenerate summand `N_m` to `Q_(m+1)`. A prefix restricts the required laws to its
  specified degree bound.
  -/
  prescribed : ∀ m : ℕ, Fin (m + 1) → (s.splitting.N m ⟶ Q.left.obj (op ⦋m + 1⦌))
  /--
  The zero face of the degree-zero whole-source prism operator is the degree-zero
  component `g₀` of the second endpoint map.
  -/
  zeroFace : operator s.splitting prescribed 0 0 (by omega) ≫ Q.left.δ (0 : Fin 2) =
    g.left.app (op ⦋0⦌)
  /--
  The one face of the degree-zero whole-source prism operator is the degree-zero
  component `f₀` of the first endpoint map.
  -/
  lastZeroFace : operator s.splitting prescribed 0 0 (by omega) ≫ Q.left.δ (1 : Fin 2) =
    f.left.app (op ⦋0⦌)
  /--
  For each `d + 1 ≤ n`, the whole-source operators in degrees `d` and `d + 1` satisfy
  the two endpoint, early-face, late-face, and common-middle prism equations.
  -/
  faces : ∀ d : ℕ, d + 1 ≤ n → Faces s.splitting prescribed f.left g.left d
  /--
  For each `m ≤ n` and `r ≤ m`, the prism operator `P_m → Q_(m+1)` followed by the
  target augmentation equals the source augmentation `P_m → A`.
  -/
  augmentation : ∀ (m : ℕ), m ≤ n → ∀ (r : ℕ) (hr : r ≤ m),
    operator s.splitting prescribed m r hr ≫ Q.hom.app (op ⦋m + 1⦌) = P.hom.app (op ⦋m⦌)

/--
The total primitive family using the zero-degree edge and the first and second
degree-one prisms in degrees zero and one. In every higher degree, the placeholder
is polynomial evaluation with all variables sent to zero.
-/
def initialPrescriptions (hQ : additiveResolutionCondition k A Q) :
    ∀ m : ℕ, Fin (m + 1) → (s.splitting.N m ⟶ Q.left.obj (op ⦋m + 1⦌)) :=
  fun m => match m with
  | 0 => fun _ => s.splitting.ι 0 ≫ PolynomialPrismFirstNondegenerateTriangle.baseEdge s f g hQ
  | 1 => fun i => s.splitting.ι 1 ≫ (if i = 0 then PolynomialPrismDegreeOne.first s f g hQ
      else PolynomialPrismDegreeOne.second s f g hQ)
  | m + 2 => fun _ => (s.polynomialIso (m + 2)).hom ≫
      CommAlgCat.ofHom (MvPolynomial.aeval (fun _ => 0))

/--
The degree-zero whole-source operator obtained from `initialPrescriptions` is the
constructed polynomial base edge.
-/
theorem initial_zero (hQ : additiveResolutionCondition k A Q) :
    operator s.splitting (initialPrescriptions s f g hQ) 0 0 (by omega) =
      PolynomialPrismFirstNondegenerateTriangle.baseEdge s f g hQ := by
  letI : IsIso (s.splitting.ι 0) := by
    change IsIso s.splitting.zeroIso.hom
    infer_instance
  apply (cancel_epi (s.splitting.ι 0)).mp
  rw [s.splitting.prismDegree_distinguished]
  rfl

/--
The vertex-zero whole-source operator in degree one obtained from the initial
prescriptions is the first degree-one prism map.
-/
theorem initial_first (hQ : additiveResolutionCondition k A Q) :
    operator s.splitting (initialPrescriptions s f g hQ) 1 0 (by omega) =
      PolynomialPrismDegreeOne.first s f g hQ := by
  apply s.splitting.one_hom_ext
  · rw [s.splitting.prismDegree_distinguished]
    rfl
  · simp only [Category.assoc]
    have hd : P.left.σ (0 : Fin 1) ≫
        operator s.splitting (initialPrescriptions s f g hQ) 1 0 (by omega) =
        operator s.splitting (initialPrescriptions s f g hQ) 0 0 (by omega) ≫ Q.left.σ (1 : Fin 2) := by
      have hc : (0 : Fin 1).castSucc = (0 : Fin 2) := Fin.ext rfl
      have hs : (0 : Fin 1).succ = (1 : Fin 2) := Fin.ext rfl
      have h₀ : (⟨0, by omega⟩ : Fin 1) = (0 : Fin 1) := Fin.ext rfl
      have h₁ : (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) := Fin.ext rfl
      have h := s.splitting.prismDegree_degeneracy_succ (n := 0)
        (initialPrescriptions s f g hQ) (0 : Fin 1) (0 : Fin 1) le_rfl
      rw [hc, hs] at h
      exact h
    rw [hd, PolynomialPrismDegreeOne.first_degeneracy s f g hQ, initial_zero s f g hQ]

/--
The vertex-one whole-source operator in degree one obtained from the initial
prescriptions is the second degree-one prism map.
-/
theorem initial_second (hQ : additiveResolutionCondition k A Q) :
    operator s.splitting (initialPrescriptions s f g hQ) 1 1 (by omega) =
      PolynomialPrismDegreeOne.second s f g hQ := by
  apply s.splitting.one_hom_ext
  · rw [s.splitting.prismDegree_distinguished]
    rfl
  · simp only [Category.assoc]
    have hd : P.left.σ (0 : Fin 1) ≫
        operator s.splitting (initialPrescriptions s f g hQ) 1 1 (by omega) =
        operator s.splitting (initialPrescriptions s f g hQ) 0 0 (by omega) ≫ Q.left.σ (0 : Fin 2) := by
      have hc : (0 : Fin 1).castSucc = (0 : Fin 2) := Fin.ext rfl
      have hs : (0 : Fin 1).succ = (1 : Fin 2) := Fin.ext rfl
      have h₀ : (⟨0, by omega⟩ : Fin 1) = (0 : Fin 1) := Fin.ext rfl
      have h₁ : (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
      have h := s.splitting.prismDegree_degeneracy_castSucc (n := 0)
        (initialPrescriptions s f g hQ) (0 : Fin 1) (0 : Fin 1) le_rfl
      rw [hc, hs] at h
      exact h
    rw [hd, PolynomialPrismDegreeOne.second_degeneracy s f g hQ, initial_zero s f g hQ]

/--
The two endpoint, early-face, late-face, and common-middle equations relating the
initial degree-one prism maps to the zero-degree base edge.
-/
def initialFaces (hQ : additiveResolutionCondition k A Q) :
    Faces s.splitting (initialPrescriptions s f g hQ) f.left g.left 0 where
  zero := by rw [initial_first]; exact PolynomialPrismDegreeOne.first_zero_face s f g hQ
  last := by rw [initial_second]; exact PolynomialPrismDegreeOne.second_last_face s f g hQ
  early := by
    intro r hr j hj
    have hr' : r = 1 := by omega
    have hj' : j = 0 := by omega
    subst r
    subst j
    rw [initial_second, initial_zero]
    exact PolynomialPrismDegreeOne.second_zero_face s f g hQ
  late := by
    intro r hr j hj hj'
    have hr' : r = 0 := by omega
    have hj'' : j = 2 := by omega
    subst r
    subst j
    rw [initial_first, initial_zero]
    exact PolynomialPrismDegreeOne.first_last_face s f g hQ
  middle := by
    intro r hr
    have hr' : r = 0 := by omega
    subst r
    rw [initial_second, initial_first]
    exact PolynomialPrismDegreeOne.middle_gluing s f g hQ

/--
The prefix through source degree one constructed from the base edge and degree-one
prism maps under additive asphericity of the target.
-/
def initial (hQ : additiveResolutionCondition k A Q) : Prefix s f g 1 where
  prescribed := initialPrescriptions s f g hQ
  zeroFace := by rw [initial_zero]; exact PolynomialPrismFirstNondegenerateTriangle.baseEdge_zero_face s f g hQ
  lastZeroFace := by rw [initial_zero]; exact PolynomialPrismFirstNondegenerateTriangle.baseEdge_one_face s f g hQ
  faces := by
    intro d hd
    have hd' : d = 0 := by omega
    subst d
    exact initialFaces s f g hQ
  augmentation := by
    intro m hm r hr
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · have hr' : r = 0 := by omega
      subst r
      rw [initial_zero]
      exact PolynomialPrismFirstNondegenerateTriangle.baseEdge_augmentation s f g hQ
    · have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with rfl | rfl
      · rw [initial_first]; exact PolynomialPrismDegreeOne.first_augmentation s f g hQ
      · rw [initial_second]; exact PolynomialPrismDegreeOne.second_augmentation s f g hQ

/--
The face data required to extend the nondegenerate prism in degree `d + 2`, obtained
from the whole-source operators and face equations of a prefix through degree `d + 1`.
-/
def previousFaces (d : ℕ) (b : Prefix s f g (d + 1)) :
    PolynomialPrismNondegenerateDegreeExtension.PreviousFaces s b.prescribed f g d where
  zero := (b.faces d le_rfl).zero
  last := (b.faces d le_rfl).last
  early := (b.faces d le_rfl).early
  late := (b.faces d le_rfl).late
  middle := (b.faces d le_rfl).middle
  augmentation := b.augmentation (d + 1) le_rfl

/--
The total primitive family obtained by replacing degree `d + 2` with the newly
constructed nondegenerate prism family and retaining the previous prescription in
every other degree.
-/
def updatedPrescriptions (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) :
    ∀ m : ℕ, Fin (m + 1) → (s.splitting.N m ⟶ Q.left.obj (op ⦋m + 1⦌)) :=
  fun m => if he : m = d + 2 then by
    subst m
    exact PolynomialPrismNondegenerateDegreeExtension.generatorPrism s b.prescribed f g
      (previousFaces s f g d b) hQ
  else b.prescribed m

/--
In degree `d + 2`, the updated primitive family is the nondegenerate generator-prism
family constructed from the preceding face data and target additive asphericity.
-/
theorem updated_new (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) :
    updatedPrescriptions s f g d b hQ (d + 2) =
      PolynomialPrismNondegenerateDegreeExtension.generatorPrism s b.prescribed f g
        (previousFaces s f g d b) hQ := by
  rw [updatedPrescriptions, dite_eq_left rfl]

/--
In every source degree `m < d + 2`, the updated primitive prescription is exactly
the preceding prefix's prescription.
-/
theorem updated_old (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) (m : ℕ) (hm : m < d + 2) :
    updatedPrescriptions s f g d b hQ m = b.prescribed m := by
  rw [updatedPrescriptions, dite_eq_right (by omega)]

/--
For each source degree `m < d + 2` and vertex `r ≤ m`, descent of the updated
prescriptions gives exactly the previous whole-source prism operator.
-/
theorem operator_unchanged (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) (m : ℕ) (hm : m < d + 2) (r : ℕ) (hr : r ≤ m) :
    operator s.splitting (updatedPrescriptions s f g d b hQ) m r hr =
      operator s.splitting b.prescribed m r hr := by
  apply s.splitting.hom_ext'
  intro t
  rw [s.splitting.prismDegree_summand, s.splitting.prismDegree_summand]
  have ht : t.1.unop.len ≤ m := SimplexCategory.len_le_of_epi t.e
  rw [updated_old s f g d b hQ t.1.unop.len (by omega)]

/--
The relative prism face equations for each earlier degree pair `j, j + 1` with
`j + 1 < d + 2`, using the updated primitive prescriptions.
-/
def oldFacesUnderUpdate (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) (j : ℕ) (hj : j + 1 < d + 2) :
    Faces s.splitting (updatedPrescriptions s f g d b hQ) f.left g.left j where
  zero := by
    rw [operator_unchanged s f g d b hQ (j + 1) hj]
    exact (b.faces j (by omega)).zero
  last := by
    rw [operator_unchanged s f g d b hQ (j + 1) hj]
    exact (b.faces j (by omega)).last
  early := by
    intro r hr i hi
    rw [operator_unchanged s f g d b hQ (j + 1) hj,
      operator_unchanged s f g d b hQ j (by omega)]
    exact (b.faces j (by omega)).early r hr i hi
  late := by
    intro r hr i hi hi'
    rw [operator_unchanged s f g d b hQ (j + 1) hj,
      operator_unchanged s f g d b hQ j (by omega)]
    exact (b.faces j (by omega)).late r hr i hi hi'
  middle := by
    intro r hr
    simp only [operator_unchanged s f g d b hQ (j + 1) hj]
    exact (b.faces j (by omega)).middle r hr

@[reassoc]
private theorem new_operator (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 3)) :
    s.splitting.ι (d + 2) ≫ s.splitting.prismDegree (updatedPrescriptions s f g d b hQ) i =
      PolynomialPrismNondegenerateDegreeExtension.generatorPrism s b.prescribed f g
        (previousFaces s f g d b) hQ i := by
  rw [s.splitting.prismDegree_distinguished, updated_new]

/--
The two endpoint, early-face, late-face, and common-middle equations in source
degree `d + 2`, after restriction to its nondegenerate summand.
-/
def newFacesOnGenerators (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) :
    FacesOnGenerators s.splitting (updatedPrescriptions s f g d b hQ) f.left g.left (d + 1) where
  zero := by
    rw [new_operator_assoc]
    exact PolynomialPrismNondegenerateDegreeExtension.generatorPrism_first_endpoint
      s b.prescribed f g (previousFaces s f g d b) hQ
  last := by
    rw [new_operator_assoc]
    exact PolynomialPrismNondegenerateDegreeExtension.generatorPrism_last_endpoint
      s b.prescribed f g (previousFaces s f g d b) hQ
  early := by
    intro r hr j hj
    rw [new_operator_assoc, operator_unchanged s f g d b hQ (d + 1) (by omega)]
    simpa only [Category.assoc, CategoryTheory.SimplicialObject.SplittingPrismFaceDescent.face,
      PolynomialOrderedPrismShell.face, CategoryTheory.SimplicialObject.SplittingPrismFaceDescent.operator,
      PolynomialPrismNondegenerateDegreeExtension.previous] using
      PolynomialPrismNondegenerateDegreeExtension.generatorPrism_early_face
        s b.prescribed f g (previousFaces s f g d b) hQ
          (⟨r, by omega⟩ : Fin (d + 3)) (⟨j, by omega⟩ : Fin (d + 4)) hj
  late := by
    intro r hr j hj hj'
    rw [new_operator_assoc, operator_unchanged s f g d b hQ (d + 1) (by omega)]
    simpa only [Category.assoc, CategoryTheory.SimplicialObject.SplittingPrismFaceDescent.face,
      PolynomialOrderedPrismShell.face, CategoryTheory.SimplicialObject.SplittingPrismFaceDescent.operator,
      PolynomialPrismNondegenerateDegreeExtension.previous] using
      PolynomialPrismNondegenerateDegreeExtension.generatorPrism_late_face
        s b.prescribed f g (previousFaces s f g d b) hQ
          (⟨r, by omega⟩ : Fin (d + 3)) (⟨j, by omega⟩ : Fin (d + 4)) hj
  middle := by
    intro r hr
    simp only [new_operator_assoc]
    exact PolynomialPrismNondegenerateDegreeExtension.generatorPrism_common_middle
      s b.prescribed f g (previousFaces s f g d b) hQ (⟨r, by omega⟩ : Fin (d + 2))

/--
Every updated whole-source prism `P_(d+2) → Q_(d+3)` has augmentation equal to the
source augmentation `P_(d+2) → A`.
-/
theorem new_augmentation (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) (r : ℕ) (hr : r ≤ d + 2) :
    operator s.splitting (updatedPrescriptions s f g d b hQ) (d + 2) r hr ≫
      Q.hom.app (op ⦋d + 3⦌) = P.hom.app (op ⦋d + 2⦌) := by
  apply augmentation_descend s.splitting (updatedPrescriptions s f g d b hQ) P.hom Q.hom
  · intro i hi
    rw [operator_unchanged s f g d b hQ (d + 1) (by omega)]
    exact b.augmentation (d + 1) le_rfl i hi
  · intro i hi
    rw [new_operator_assoc]
    exact PolynomialPrismNondegenerateDegreeExtension.generatorPrism_augmentation
      s b.prescribed f g (previousFaces s f g d b) hQ (⟨i, by omega⟩ : Fin (d + 3))

/--
The extension of a prefix through degree `d + 1` to a prefix through degree `d + 2`,
using the target's additive asphericity to fill the new polynomial degree and retaining
the preceding degrees.
-/
def extend (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) : Prefix s f g (d + 2) where
  prescribed := updatedPrescriptions s f g d b hQ
  zeroFace := by rw [operator_unchanged s f g d b hQ 0 (by omega)]; exact b.zeroFace
  lastZeroFace := by rw [operator_unchanged s f g d b hQ 0 (by omega)]; exact b.lastZeroFace
  faces := by
    intro j hj
    by_cases he : j = d + 1
    · subst j
      exact descend s.splitting (updatedPrescriptions s f g d b hQ) f.left g.left
        (oldFacesUnderUpdate s f g d b hQ d (by omega)) (newFacesOnGenerators s f g d b hQ)
    · exact oldFacesUnderUpdate s f g d b hQ j (by omega)
  augmentation := by
    intro m hm r hr
    by_cases he : m = d + 2
    · subst m
      exact new_augmentation s f g d b hQ r hr
    · rw [operator_unchanged s f g d b hQ m (by omega)]
      exact b.augmentation m (by omega) r hr

/--
The successor prefix has exactly the same primitive prescription as its predecessor
in every degree `m < d + 2`.
-/
theorem extend_prescribed_old (d : ℕ) (b : Prefix s f g (d + 1))
    (hQ : additiveResolutionCondition k A Q) (m : ℕ) (hm : m < d + 2) :
    (extend s f g d b hQ).prescribed m = b.prescribed m :=
  updated_old s f g d b hQ m hm

end CommAlgCat.PolynomialPrismDegreeAssembly

end
