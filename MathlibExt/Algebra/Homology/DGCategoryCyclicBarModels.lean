/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModelContracts
public import MathlibExt.CategoryTheory.MonoidalTensorWordModels
public import MathlibExt.Algebra.Homology.DGCyclicMixedModels
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The actual cyclic bar terms of an arbitrary DG category

The n-th term is the native coproduct over all cyclic strings of n+1
objects, of the tensor word of their actual Hom complexes. Rotation uses
the native cochain braiding and its Koszul signs. Faces compose adjacent
Hom factors; degeneracies insert the source identities. No one-object
algebra restriction or independent face/cyclic operator is imposed.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, §2.1;
Keller, On differential graded categories, §5; Loday, Cyclic homology,
§1.1. Native DG and cochain tensor proofs retain their pinned source
author/license notices in DGSource.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.MonoidalTensorWordModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- A path has its literal DG Hom complex at each consecutive pair of objects. -/
def pathFactors (C : DGCat k) (a : C) : List C → C → List (Cochains k)
  | [], b => [dgHomComplex k a b]
  | x :: xs, b => dgHomComplex k a x :: pathFactors C x xs b

/-- The actual cochain tensor word of an object path. -/
def pathTensor (C : DGCat k) (a : C) (xs : List C) (b : C) : Cochains k :=
  word (pathFactors C a xs b)

/-- A cyclic string has one distinguished initial object and n further objects. -/
structure CyclicObjects (C : DGCat k) (n : ℕ) where
  root : C
  tail : Fin n → C

/-- The actual tensor word around this closed object string. -/
def cycleTensor (C : DGCat k) {n : ℕ} (s : CyclicObjects C n) : Cochains k :=
  pathTensor C s.root (List.ofFn s.tail) s.root

/-- Every object string contributes its native Hom tensor word. -/
def barTerm (C : DGCat k) (n : ℕ) : Cochains k :=
  ∐ fun s : CyclicObjects C n => cycleTensor C s

/-- A path ending with one additional object splits before its last Hom factor. -/
theorem pathFactors_append_last (C : DGCat k) (a b c : C) (xs : List C) :
    pathFactors C a (xs ++ [b]) c =
      pathFactors C a xs b ++ [dgHomComplex k b c] := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, pathFactors, ih]

/-- The last object becomes the initial one, with the other objects cyclically reordered. -/
def rotatedObjects (C : DGCat k) : (n : ℕ) → CyclicObjects C n → CyclicObjects C n
  | 0, s => s
  | n + 1, s =>
    ⟨s.tail (Fin.last n), Fin.cons s.root (fun i : Fin n => s.tail i.castSucc)⟩

/-- Rotation of a Hom word is the actual last-factor cochain braiding. -/
def rotationWordIso (C : DGCat k) : (n : ℕ) → (s : CyclicObjects C n) →
    cycleTensor C s ≅ cycleTensor C (rotatedObjects C n s)
  | 0, s => Iso.refl _
  | n + 1, s =>
    let y := s.tail (Fin.last n)
    let xs := List.ofFn (fun i : Fin n => s.tail i.castSucc)
    eqToIso (by
      dsimp [cycleTensor, pathTensor]
      rw [List.ofFn_succ', List.concat_eq_append, pathFactors_append_last]) ≪≫
      rotateLast (pathFactors C s.root xs y) (dgHomComplex k y s.root) ≪≫
      eqToIso (by
        dsimp [cycleTensor, pathTensor, rotatedObjects, xs, y]
        rw [List.ofFn_succ]
        rfl)

/-- Native coproduct assembly of the actual cyclic word maps. -/
def rotation (C : DGCat k) (n : ℕ) : barTerm C n ⟶ barTerm C n :=
  Sigma.desc (fun s => (rotationWordIso C n s).hom ≫
    Sigma.ι (fun t : CyclicObjects C n => cycleTensor C t) (rotatedObjects C n s))

/-- Every cyclic power is iteration of the same computed word rotation. -/
def rotationPower (C : DGCat k) (n : ℕ) : ℕ → (barTerm C n ⟶ barTerm C n)
  | 0 => 𝟙 _
  | m + 1 => rotationPower C n m ≫ rotation C n

/-- Remove the first intermediate object by actual enriched composition. -/
def contractFirst (C : DGCat k) (a y : C) : (xs : List C) → (b : C) →
    pathTensor C a (y :: xs) b ⟶ pathTensor C a xs b
  | [], b => contractHead (eComp (Cochains k) a y b) []
  | z :: zs, b => contractHead (eComp (Cochains k) a y z) (pathFactors C z zs b)

/-- The initial multiplication face deletes exactly the first intermediate vertex. -/
def headFaceWord (C : DGCat k) (n : ℕ) (s : CyclicObjects C (n + 1)) :
    cycleTensor C s ⟶ cycleTensor C (⟨s.root, Fin.tail s.tail⟩ : CyclicObjects C n) :=
  eqToHom (by dsimp [cycleTensor, pathTensor]; rw [List.ofFn_succ]; rfl) ≫
    contractFirst C s.root (s.tail 0) (List.ofFn (Fin.tail s.tail)) s.root

/-- The initial face is assembled on all actual object strings. -/
def headFace (C : DGCat k) (n : ℕ) : barTerm C (n + 1) ⟶ barTerm C n :=
  Sigma.desc (fun s => headFaceWord C n s ≫
    Sigma.ι (fun t : CyclicObjects C n => cycleTensor C t) ⟨s.root, Fin.tail s.tail⟩)

/-- All faces are the native adjacent-composition face in its actual cyclic position.
The last face rotates the closing factor to the front before composing. -/
def face (C : DGCat k) (n : ℕ) (i : Fin (n + 2)) : barTerm C (n + 1) ⟶ barTerm C n :=
  rotationPower C (n + 1) ((n + 2 - i.val) % (n + 2)) ≫
    headFace C n ≫ rotationPower C n (i.val % (n + 1))

/-- The extra bar degeneracy duplicates the actual distinguished object. -/
def extraObjects (C : DGCat k) {n : ℕ} (s : CyclicObjects C n) : CyclicObjects C (n + 1) :=
  ⟨s.root, Fin.cons s.root s.tail⟩

/-- The extra degeneracy inserts the literal DG identity before the Hom word. -/
def extraWord (C : DGCat k) {n : ℕ} (s : CyclicObjects C n) :
    cycleTensor C s ⟶ cycleTensor C (extraObjects C s) :=
  (λ_ (cycleTensor C s)).inv ≫
    (eId (Cochains k) s.root ⊗ₘ 𝟙 (cycleTensor C s)) ≫
      eqToHom (by
        dsimp [cycleTensor, pathTensor, extraObjects]
        rw [List.ofFn_succ]
        rfl)

/-- Unit insertion is assembled from the same native identities on every object string. -/
def extraDegeneracy (C : DGCat k) (n : ℕ) : barTerm C n ⟶ barTerm C (n + 1) :=
  Sigma.desc (fun s => extraWord C s ≫
    Sigma.ι (fun t : CyclicObjects C (n + 1) => cycleTensor C t) (extraObjects C s))

/-- Ordinary degeneracies insert the identity after the indicated actual Hom factor. -/
def degeneracy (C : DGCat k) (n : ℕ) (i : Fin (n + 1)) : barTerm C n ⟶ barTerm C (n + 1) :=
  rotationPower C n ((n + 1 - ((i.val + 1) % (n + 1))) % (n + 1)) ≫
    extraDegeneracy C n ≫ rotationPower C (n + 1) (i.val + 1)

/-- A DG functor maps every path by its actual Hom maps, with native tensor functoriality. -/
def mapPathTensor {C D : DGCat k} (F : C ⟶ D) (a : C) : (xs : List C) → (b : C) →
    pathTensor C a xs b ⟶ pathTensor D (F.obj a) (xs.map F.obj) (F.obj b)
  | [], b => F.map a b ⊗ₘ 𝟙 (𝟙_ (Cochains k))
  | z :: zs, b => F.map a z ⊗ₘ mapPathTensor F z zs b

/-- The same actual DG images define the target object cycle. -/
def mappedObjects {C D : DGCat k} (F : C ⟶ D) {n : ℕ} (s : CyclicObjects C n) :
    CyclicObjects D n := ⟨F.obj s.root, fun i => F.obj (s.tail i)⟩

/-- The cochain map on one cycle fixes every actual tensor factor. -/
def mapCycleTensor {C D : DGCat k} (F : C ⟶ D) {n : ℕ} (s : CyclicObjects C n) :
    cycleTensor C s ⟶ cycleTensor D (mappedObjects F s) :=
  mapPathTensor F s.root (List.ofFn s.tail) s.root ≫
    eqToHom (by
      dsimp [cycleTensor, pathTensor, mappedObjects]
      rw [List.map_ofFn]
      rfl)

/-- Functorial bar maps are assembled on the same literal coproduct generators. -/
def barMap {C D : DGCat k} (F : C ⟶ D) (n : ℕ) : barTerm C n ⟶ barTerm D n :=
  Sigma.desc (fun s => mapCycleTensor F s ≫
    Sigma.ι (fun t : CyclicObjects D n => cycleTensor D t) (mappedObjects F s))

/-- Assembly of the actual cyclic bar functor preserves its fixed faces and units. -/
structure CyclicBarModel (C : DGCat k) where
  simplicial : SimplicialObject (Cochains k)
  termIso : ∀ n : ℕ, simplicial.obj (op ⦋n⦌) ≅ barTerm C n
  face_eq : ∀ (n : ℕ) (i : Fin (n + 2)),
    simplicial.δ i ≫ (termIso n).hom = (termIso (n + 1)).hom ≫ face C n i
  degeneracy_eq : ∀ (n : ℕ) (i : Fin (n + 1)),
    simplicial.σ i ≫ (termIso (n + 1)).hom = (termIso n).hom ≫ degeneracy C n i
  rotation_order : ∀ n : ℕ, rotationPower C n (n + 1) = 𝟙 (barTerm C n)

end MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
