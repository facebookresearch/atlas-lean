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

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# Finite tensor powers of cochain complexes

Let R be a commutative ring and X a cochain complex of R-modules indexed by ℤ. Using the given
graded tensor coproducts, define P₀(X) = 𝟙 and Pₙ₊₁(X) = Pₙ(X) ⊗ X. A cochain map f induces
P₀(f) = id and Pₙ₊₁(f) = Pₙ(f) ⊗ f. These maps preserve identities and composition. The binary
tensor product has the cohomological differential d(x ⊗ y) = d(x) ⊗ y + (−1)^i x ⊗ d(y) for
homogeneous x of degree i.

The unit and associativity comparisons additionally use preservation of empty colimits by both
module tensor functors, the four-factor graded tensor-object extensionality structure and the
two graded iterated-tensor coproduct structures. They give block-splitting isomorphisms
a_{m,n} : P_{m+n}(X) ≅ P_m(X) ⊗ P_n(X), natural in X and coherent under triple splitting,
including zero-sized blocks.

Under these monoidal hypotheses, the recursive power objects equal the general monoidal
tensor-power objects. The induced object comparisons commute with power maps and with both
orientations of the block-splitting isomorphisms. Every power is a finite binary iteration
with the displayed left association.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]

/-- Left-associated finite tensor power of a cochain complex.

For a cochain complex X over a commutative ring R, with the graded tensor coproducts defined,
set P₀(X) to the cochain tensor unit and Pₙ₊₁(X) = Pₙ(X) ⊗ X. The recursion retains the left
association and the initial unit factor. -/
noncomputable def tensorPowObj (X : CochainComplex (ModuleCat R) ℤ) :
    ℕ → CochainComplex (ModuleCat R) ℤ
  | 0 => HomologicalComplex.tensorUnit _ _
  | n + 1 => HomologicalComplex.tensorObj (tensorPowObj X n) X

/-- Zeroth cochain tensor power.

For a cochain complex X over R, its zeroth recursive tensor power is the cochain tensor unit,
concentrated in degree zero at the scalar module R. -/
@[simp]
theorem tensorPowObj_zero (X : CochainComplex (ModuleCat R) ℤ) :
    tensorPowObj X 0 = HomologicalComplex.tensorUnit _ _ :=
  rfl

/-- Successor cochain tensor power.

For every n : ℕ, Pₙ₊₁(X) is the binary cochain tensor product Pₙ(X) ⊗ X, with the graded
tensor coproduct structures assumed in the construction. -/
@[simp]
theorem tensorPowObj_succ (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    tensorPowObj X (n + 1) =
      HomologicalComplex.tensorObj (tensorPowObj X n) X :=
  rfl

/-- Map on recursive cochain tensor powers.

For a cochain map f : X → Y, define P₀(f) = id on the tensor unit and Pₙ₊₁(f) = Pₙ(f) ⊗ f. The
binary tensor maps use the given graded tensor coproducts. -/
noncomputable def tensorPowMap {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) : ∀ (n : ℕ), tensorPowObj X n ⟶ tensorPowObj Y n
  | 0 => 𝟙 _
  | n + 1 => HomologicalComplex.tensorHom (tensorPowMap f n) f

/-- Map on the zeroth tensor power.

For every cochain map f : X → Y over R, P₀(f) is the identity of the cochain tensor unit,
independently of f. -/
@[simp]
theorem tensorPowMap_zero {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) : tensorPowMap f 0 = 𝟙 _ :=
  rfl

/-- Map on a successor tensor power.

For f : X → Y and n : ℕ, the recursive power map is Pₙ₊₁(f) = Pₙ(f) ⊗ f from Pₙ(X) ⊗ X to
Pₙ(Y) ⊗ Y. -/
@[simp]
theorem tensorPowMap_succ {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) (n : ℕ) :
    tensorPowMap f (n + 1) =
      HomologicalComplex.tensorHom (tensorPowMap f n) f :=
  rfl

/-- Identity law for cochain tensor powers.

For a cochain complex X over R and any natural n, the power map Pₙ(id_X) is id_{Pₙ(X)}. The
binary tensor identity law is applied through the left-associated recursion. -/
@[simp]
theorem tensorPowMap_id (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    tensorPowMap (𝟙 X) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change HomologicalComplex.tensorHom (tensorPowMap (𝟙 X) n) (𝟙 X) = 𝟙 _
    rw [ih]
    exact HomologicalComplex.tensorHom_id_id _ _

/-- Composition law for cochain tensor powers.

For cochain maps f : X → Y and g : Y → Z, Pₙ(f ≫ g) = Pₙ(f) ≫ Pₙ(g) for every n : ℕ. This
retains the same binary tensor-map order at each successor step. -/
theorem tensorPowMap_comp {X Y Z : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    tensorPowMap (f ≫ g) n = tensorPowMap f n ≫ tensorPowMap g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change HomologicalComplex.tensorHom (tensorPowMap (f ≫ g) n) (f ≫ g) =
      HomologicalComplex.tensorHom (tensorPowMap f n) f ≫
        HomologicalComplex.tensorHom (tensorPowMap g n) g
    rw [ih]
    exact (HomologicalComplex.tensorHom_comp_tensorHom _ _ _ _).symm

/-- Finite tensor-power functor on cochain complexes.

For a fixed n : ℕ, the assignment X ↦ Pₙ(X), f ↦ Pₙ(f) defines a functor on
CochainComplex(ModuleCat R,ℤ), using the specified graded binary tensor coproducts. -/
noncomputable def tensorPowFunctor (n : ℕ) :
    CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat R) ℤ where
  obj X := tensorPowObj X n
  map f := tensorPowMap f n
  map_id X := tensorPowMap_id X n
  map_comp f g := tensorPowMap_comp f g n

/-- Object value of the cochain tensor-power functor.

For a cochain complex X and fixed n, tensorPowFunctor n takes X to tensorPowObj X n, the
recursive left-associated power starting from the tensor unit. -/
@[simp]
theorem tensorPowFunctor_obj (n : ℕ) (X : CochainComplex (ModuleCat R) ℤ) :
    (tensorPowFunctor n).obj X = tensorPowObj X n :=
  rfl

/-- Morphism value of the cochain tensor-power functor.

For f : X → Y and fixed n, tensorPowFunctor n takes f to tensorPowMap f n, with zeroth map
identity and successor map Pₙ(f) ⊗ f. -/
@[simp]
theorem tensorPowFunctor_map (n : ℕ) {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) : (tensorPowFunctor n).map f = tensorPowMap f n :=
  rfl

/-- Tensoring a cochain isomorphism with a fixed right factor.

For a cochain isomorphism e : A ≅ B and fixed cochain complex C, the binary tensor structures
give A ⊗ C ≅ B ⊗ C. Its hom is e.hom ⊗ id_C and its inverse is e.inv ⊗ id_C. -/
noncomputable def tensorIsoRight
    {A B C : CochainComplex (ModuleCat R) ℤ} (e : A ≅ B) :
    HomologicalComplex.tensorObj A C ≅ HomologicalComplex.tensorObj B C where
  hom := HomologicalComplex.tensorHom e.hom (𝟙 C)
  inv := HomologicalComplex.tensorHom e.inv (𝟙 C)
  hom_inv_id := by
    rw [HomologicalComplex.tensorHom_comp_tensorHom]
    simp only [CategoryTheory.Iso.hom_inv_id,
      CategoryTheory.Category.id_comp, HomologicalComplex.tensorHom_id_id]
  inv_hom_id := by
    rw [HomologicalComplex.tensorHom_comp_tensorHom]
    simp only [CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Category.id_comp, HomologicalComplex.tensorHom_id_id]

/-- Vanishing of a cochain tensor map with zero right factor.

For a cochain map f : K₁ → L₁, the binary tensor map f ⊗ 0 : K₁ ⊗ K₂ → L₁ ⊗ L₂ is zero, with
the graded tensor coproducts defined. -/
theorem tensorHom_zero {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat R) ℤ}
    (f : K₁ ⟶ L₁) :
    HomologicalComplex.tensorHom f (0 : K₂ ⟶ L₂) = 0 := by
  exact HomologicalComplex.tensorHom_zero f

/-- Vanishing of a cochain tensor map with zero left factor.

For a cochain map g : K₂ → L₂, the binary tensor map 0 ⊗ g : K₁ ⊗ K₂ → L₁ ⊗ L₂ is zero, with
the graded tensor coproducts defined. -/
theorem zero_tensorHom {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat R) ℤ}
    (g : K₂ ⟶ L₂) :
    HomologicalComplex.tensorHom (0 : K₁ ⟶ L₁) g = 0 := by
  exact HomologicalComplex.zero_tensorHom g

section AddCoherence

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

/-- Splitting a finite cochain tensor power into two blocks.

With the given graded coproduct hypotheses defining cochain unitors and associators, construct
a_{m,n} : P_{m+n}(X) ≅ P_m(X) ⊗ P_n(X). At n = 0 this is the inverse right unitor after the
index equality m+0 = m. At a successor it tensors a_{m,n} with id_X on the right and then
applies the associator. -/
@[nolint defsWithUnderscore]
noncomputable def tensorPowObj_add (X : CochainComplex (ModuleCat R) ℤ)
    (m : ℕ) : ∀ (n : ℕ),
    tensorPowObj X (m + n) ≅
      HomologicalComplex.tensorObj (tensorPowObj X m) (tensorPowObj X n)
  | 0 =>
    eqToIso (congrArg (tensorPowObj X) (Nat.add_zero m)) ≪≫
      (HomologicalComplex.rightUnitor _).symm
  | n + 1 =>
    eqToIso (congrArg (tensorPowObj X) (Nat.add_succ m n)) ≪≫
      (tensorIsoRight (tensorPowObj_add X m n)) ≪≫
        HomologicalComplex.associator _ _ _

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Right-unit formula for a tensor-power block split.

For the splitting a_{m,0}, its hom is the map induced by P_{m+0}(X) = P_m(X), followed by the
inverse cochain right unitor P_m(X) → P_m(X) ⊗ 𝟙. The stated graded coproduct and right-unit
hypotheses define these maps. -/
theorem tensorPowObj_add_zero_right
    (X : CochainComplex (ModuleCat R) ℤ) (m : ℕ) :
    (tensorPowObj_add X m 0).hom =
      (eqToIso (congrArg (tensorPowObj X) (Nat.add_zero m))).hom ≫
        (HomologicalComplex.rightUnitor _).symm.hom :=
  rfl

/-- Left-unit formula for a tensor-power block split.

With cochain tensor unitors and associators defined by the graded coproduct hypotheses,
a_{0,n}.hom followed by the left unitor of P_n(X) is the map induced by P_{0+n}(X) = P_n(X).
This retains the canonical index-identification map at n = 0 as well. -/
theorem tensorPowObj_add_zero_left
    (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    (tensorPowObj_add X 0 n).hom ≫
        (HomologicalComplex.leftUnitor (tensorPowObj X n)).hom =
      (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add n))).hom := by
  induction n with
  | zero =>
    have hR : (eqToIso (congrArg (tensorPowObj X) (Nat.add_zero 0))).hom
        = 𝟙 _ := rfl
    rw [tensorPowObj_add_zero_right, hR,
      CategoryTheory.Category.id_comp] at ⊢
    change (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).inv ≫
        (HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).hom =
      𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
    have hLU : HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) =
        CategoryTheory.MonoidalCategory.leftUnitor _ := rfl
    have hRU : HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) =
        CategoryTheory.MonoidalCategory.rightUnitor _ := rfl
    have hUE : (CategoryTheory.MonoidalCategory.leftUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).hom =
        (CategoryTheory.MonoidalCategory.rightUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).hom :=
      CategoryTheory.MonoidalCategory.unitors_equal
    rw [hLU, hRU, hUE, CategoryTheory.Iso.inv_hom_id]
  | succ n ih =>
    have hY0 : (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ 0 n))).hom
        = 𝟙 _ := rfl
    have hAdd : (tensorPowObj_add X 0 (n + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ 0 n))).hom ≫
          (tensorIsoRight (tensorPowObj_add X 0 n)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X 0)
            (tensorPowObj X n) X).hom := rfl
    have hIso : (tensorIsoRight (tensorPowObj_add X 0 n)).hom =
        HomologicalComplex.tensorHom (tensorPowObj_add X 0 n).hom (𝟙 X) := rfl
    rw [hAdd, hIso, hY0, CategoryTheory.Category.id_comp] at ⊢
    have hP0 : tensorPowObj X 0 =
        HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ) := rfl
    have hObj : HomologicalComplex.tensorObj (tensorPowObj X 0)
          (tensorPowObj X n) =
        HomologicalComplex.tensorObj
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) :=
      congrArg
        (fun U => HomologicalComplex.tensorObj U (tensorPowObj X n)) hP0
    let a2 : tensorPowObj X (0 + n) ⟶
        HomologicalComplex.tensorObj
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) := Eq.mpr
      (congrArg (fun U => tensorPowObj X (0 + n) ⟶
        HomologicalComplex.tensorObj U (tensorPowObj X n)) hP0)
      (tensorPowObj_add X 0 n).hom
    change HomologicalComplex.tensorHom a2 (𝟙 X) ≫
        (HomologicalComplex.associator
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) X).hom ≫
        (HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X n) X)).hom =
      (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add (n + 1)))).hom
    have hTri := CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom
      (tensorPowObj X n) X
    have hTri' : (HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X n) X)).hom =
        (HomologicalComplex.associator
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) X).inv ≫
        HomologicalComplex.tensorHom
          (HomologicalComplex.leftUnitor (tensorPowObj X n)).hom (𝟙 X) := hTri
    have ih_t : a2 ≫
          (HomologicalComplex.leftUnitor (tensorPowObj X n)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add n))).hom := ih
    rw [hTri', CategoryTheory.Iso.hom_inv_id_assoc,
      HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id, ih_t] at ⊢
    have gen : ∀ {a b : ℕ} (h : a = b),
        HomologicalComplex.tensorHom
          (eqToIso (congrArg (tensorPowObj X) h)).hom (𝟙 X) =
        (eqToIso (congrArg
          (fun k => HomologicalComplex.tensorObj (tensorPowObj X k) X) h)).hom := by
      intro a b h
      cases h
      simp [HomologicalComplex.tensorHom_id_id]
    rw [gen (Nat.zero_add n)] at ⊢
    have hD : Nat.zero_add (n + 1) = congrArg Nat.succ (Nat.zero_add n) :=
      rfl
    rw [hD] at ⊢
    rfl

/-- Naturality of the cochain tensor-power block split.

For f : X → Y and m,n : ℕ, the splitting maps satisfy P_{m+n}(f) ≫ a_{m,n}(Y).hom =
a_{m,n}(X).hom ≫ (P_m(f) ⊗ P_n(f)). The unit and associativity comparisons use the stated
graded tensor coproduct hypotheses. -/
theorem tensorPowObj_add_naturality
    {X Y : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ Y) (m n : ℕ) :
    tensorPowMap f (m + n) ≫ (tensorPowObj_add Y m n).hom =
      (tensorPowObj_add X m n).hom ≫
        HomologicalComplex.tensorHom (tensorPowMap f m) (tensorPowMap f n) := by
  induction n generalizing m with
  | zero =>
    have hY : (eqToIso (congrArg (tensorPowObj Y) (Nat.add_zero m))).hom
        = 𝟙 _ := rfl
    have hX : (eqToIso (congrArg (tensorPowObj X) (Nat.add_zero m))).hom
        = 𝟙 _ := rfl
    rw [tensorPowObj_add_zero_right, tensorPowObj_add_zero_right,
      hY, hX, CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp]
    change tensorPowMap f m ≫ (HomologicalComplex.rightUnitor _).inv =
      (HomologicalComplex.rightUnitor _).inv ≫
        HomologicalComplex.tensorHom (tensorPowMap f m) (𝟙 _)
    have h := CategoryTheory.MonoidalCategory.rightUnitor_naturality
      (tensorPowMap f m)
    have h' : HomologicalComplex.tensorHom (tensorPowMap f m) (𝟙 _) ≫
        (HomologicalComplex.rightUnitor _).hom =
        (HomologicalComplex.rightUnitor _).hom ≫ tensorPowMap f m := h
    rw [CategoryTheory.Iso.comp_inv_eq, CategoryTheory.Category.assoc, h',
      ← CategoryTheory.Category.assoc, CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Category.id_comp]
  | succ n ih =>
    have hMap : tensorPowMap f (m + (n + 1)) =
        HomologicalComplex.tensorHom (tensorPowMap f (m + n)) f := rfl
    have hMapN : tensorPowMap f (n + 1) =
        HomologicalComplex.tensorHom (tensorPowMap f n) f := rfl
    have hY0 : (eqToIso (congrArg (tensorPowObj Y) (Nat.add_succ m n))).hom
        = 𝟙 _ := rfl
    have hX0 : (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ m n))).hom
        = 𝟙 _ := rfl
    have hAddY : (tensorPowObj_add Y m (n + 1)).hom =
        (eqToIso (congrArg (tensorPowObj Y) (Nat.add_succ m n))).hom ≫
          (tensorIsoRight (tensorPowObj_add Y m n)).hom ≫
          (HomologicalComplex.associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom := rfl
    have hAddX : (tensorPowObj_add X m (n + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ m n))).hom ≫
          (tensorIsoRight (tensorPowObj_add X m n)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X n) X).hom := rfl
    have hIsoY : (tensorIsoRight (tensorPowObj_add Y m n)).hom =
        HomologicalComplex.tensorHom (tensorPowObj_add Y m n).hom (𝟙 Y) := rfl
    have hIsoX : (tensorIsoRight (tensorPowObj_add X m n)).hom =
        HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom (𝟙 X) := rfl
    rw [hMap, hAddY, hAddX, hIsoY, hIsoX, hY0, hX0,
      CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp, hMapN]
    change HomologicalComplex.tensorHom (tensorPowMap f (m + n)) f ≫
        (HomologicalComplex.tensorHom (tensorPowObj_add Y m n).hom (𝟙 Y) ≫
          (HomologicalComplex.associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom) =
      (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom (𝟙 X) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n) X).hom) ≫
        HomologicalComplex.tensorHom (tensorPowMap f m)
          (HomologicalComplex.tensorHom (tensorPowMap f n) f)
    have hNat := CategoryTheory.MonoidalCategory.associator_naturality
      (tensorPowMap f m) (tensorPowMap f n) f
    have hNat' : HomologicalComplex.tensorHom
          (HomologicalComplex.tensorHom (tensorPowMap f m) (tensorPowMap f n))
          f ≫ (HomologicalComplex.associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom =
        (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X n) X).hom ≫
          HomologicalComplex.tensorHom (tensorPowMap f m)
            (HomologicalComplex.tensorHom (tensorPowMap f n) f) := hNat
    simp only [← CategoryTheory.Category.assoc,
      HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id, ih] at ⊢
    nth_rewrite 3 [← CategoryTheory.Category.id_comp f] at ⊢
    rw [← HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.assoc, hNat',
      ← CategoryTheory.Category.assoc] at ⊢

/-- Associativity of successive tensor-power block splits.

With cochain unitors and associators defined, the two maps from P_{(m+n)+k}(X) to P_m(X) ⊗
(P_n(X) ⊗ P_k(X)) agree. The first transports along (m+n)+k = m+(n+k), then applies a_{m,n+k}
and id ⊗ a_{n,k}. The second applies a_{m+n,k}, then a_{m,n} ⊗ id, then the associator. This
holds for all m,n,k : ℕ. -/
theorem tensorPowObj_add_assoc
    (X : CochainComplex (ModuleCat R) ℤ) (m n k : ℕ) :
    (eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom ≫
        (tensorPowObj_add X m (n + k)).hom ≫
        HomologicalComplex.tensorHom (𝟙 _)
          ((tensorPowObj_add X n k).hom) =
      (tensorPowObj_add X (m + n) k).hom ≫
        HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.associator _ _ _).hom := by
  induction k with
  | zero =>
    have hr : (m + n) + 0 = m + (n + 0) := rfl
    have hAeq : Nat.add_assoc m n 0 = hr := rfl
    rw [hAeq] at ⊢
    have hA1 : (eqToIso (congrArg (tensorPowObj X) hr)).hom = 𝟙 _ := rfl
    rw [hA1, CategoryTheory.Category.id_comp] at ⊢
    have hN0 : (tensorPowObj_add X m (n + 0)).hom =
        (tensorPowObj_add X m n).hom := rfl
    rw [hN0] at ⊢
    have hR1 : (tensorPowObj_add X n 0).hom =
        (HomologicalComplex.rightUnitor (tensorPowObj X n)).symm.hom := by
      rw [tensorPowObj_add_zero_right]
      have h1 : (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_zero n))).hom = 𝟙 _ := rfl
      rw [h1, CategoryTheory.Category.id_comp]
    have hR2 : (tensorPowObj_add X (m + n) 0).hom =
        (HomologicalComplex.rightUnitor
          (tensorPowObj X (m + n))).symm.hom := by
      rw [tensorPowObj_add_zero_right]
      have h2 : (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_zero (m + n)))).hom = 𝟙 _ := rfl
      rw [h2, CategoryTheory.Category.id_comp]
    rw [hR1, hR2] at ⊢
    change (tensorPowObj_add X m n).hom ≫
        HomologicalComplex.tensorHom (𝟙 _)
          (HomologicalComplex.rightUnitor (tensorPowObj X n)).inv =
      (HomologicalComplex.rightUnitor (tensorPowObj X (m + n))).inv ≫
        HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorUnit (ModuleCat R)
            (ComplexShape.up ℤ))).hom
    have hTinv0 := CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv
      (tensorPowObj X m) (tensorPowObj X n)
    have hTinv : (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n))).inv =
        HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (HomologicalComplex.rightUnitor (tensorPowObj X n)).inv ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorUnit (ModuleCat R)
            (ComplexShape.up ℤ))).inv := hTinv0
    have hNat := CategoryTheory.MonoidalCategory.rightUnitor_naturality
      (tensorPowObj_add X m n).hom
    have hNat' : HomologicalComplex.tensorHom
          ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n))).hom =
        (HomologicalComplex.rightUnitor (tensorPowObj X (m + n))).hom ≫
          (tensorPowObj_add X m n).hom := hNat
    have hVW : (HomologicalComplex.rightUnitor
          (tensorPowObj X (m + n))).inv ≫
        HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom) (𝟙 _) =
        (tensorPowObj_add X m n).hom ≫
        (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n))).inv := by
      have h1 : (HomologicalComplex.rightUnitor
            (tensorPowObj X (m + n))).hom ≫
          ((HomologicalComplex.rightUnitor
            (tensorPowObj X (m + n))).inv ≫
          HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom)
            (𝟙 _)) =
          (HomologicalComplex.rightUnitor
            (tensorPowObj X (m + n))).hom ≫
          ((tensorPowObj_add X m n).hom ≫
          (HomologicalComplex.rightUnitor
            (HomologicalComplex.tensorObj (tensorPowObj X m)
              (tensorPowObj X n))).inv) := by
        rw [← CategoryTheory.Category.assoc,
          CategoryTheory.Iso.hom_inv_id, CategoryTheory.Category.id_comp,
          ← CategoryTheory.Category.assoc, ← hNat',
          CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id,
          CategoryTheory.Category.comp_id]
      exact (CategoryTheory.Iso.cancel_iso_hom_left
        (HomologicalComplex.rightUnitor (tensorPowObj X (m + n))) _ _).mp h1
    rw [← CategoryTheory.Category.assoc, hVW,
      CategoryTheory.Category.assoc, hTinv,
      CategoryTheory.Category.assoc, CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Category.comp_id] at ⊢
  | succ k ih =>
    have hS1 : (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_succ m (n + k)))).hom = 𝟙 _ := rfl
    have hS2 : (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_succ n k))).hom = 𝟙 _ := rfl
    have hS3 : (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_succ (m + n) k))).hom = 𝟙 _ := rfl
    have hAddR : (tensorPowObj_add X (m + n) (k + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_succ (m + n) k))).hom ≫
          (tensorIsoRight (tensorPowObj_add X (m + n) k)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X (m + n))
            (tensorPowObj X k) X).hom := rfl
    have hAddM : (tensorPowObj_add X m (n + (k + 1))).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_succ m (n + k)))).hom ≫
          (tensorIsoRight (tensorPowObj_add X m (n + k))).hom ≫
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X (n + k)) X).hom := rfl
    have hAddN : (tensorPowObj_add X n (k + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_succ n k))).hom ≫
          (tensorIsoRight (tensorPowObj_add X n k)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X n)
            (tensorPowObj X k) X).hom := rfl
    have hIsoR : (tensorIsoRight
        (tensorPowObj_add X (m + n) k)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add X (m + n) k).hom (𝟙 X) := rfl
    have hIsoM : (tensorIsoRight
        (tensorPowObj_add X m (n + k))).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add X m (n + k)).hom (𝟙 X) := rfl
    have hIsoN : (tensorIsoRight (tensorPowObj_add X n k)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add X n k).hom (𝟙 X) := rfl
    have hD : Nat.add_assoc m n (k + 1) =
        congrArg Nat.succ (Nat.add_assoc m n k) := rfl
    rw [hD] at ⊢
    rw [hAddR, hAddM, hAddN, hIsoR, hIsoM, hIsoN,
      hS1, hS2, hS3, CategoryTheory.Category.id_comp,
      CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp] at ⊢
    change (eqToIso (congrArg (fun j => HomologicalComplex.tensorObj
            (tensorPowObj X j) X) (Nat.add_assoc m n k))).hom ≫
          (HomologicalComplex.tensorHom
            (tensorPowObj_add X m (n + k)).hom (𝟙 X) ≫
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X (n + k)) X).hom) ≫
          HomologicalComplex.tensorHom (𝟙 _)
            (HomologicalComplex.tensorHom
              (tensorPowObj_add X n k).hom (𝟙 X) ≫
            (HomologicalComplex.associator (tensorPowObj X n)
              (tensorPowObj X k) X).hom) =
        (HomologicalComplex.tensorHom
          (tensorPowObj_add X (m + n) k).hom (𝟙 X) ≫
        (HomologicalComplex.associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom) ≫
        HomologicalComplex.tensorHom
          ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom
    have genX : ∀ {a b : ℕ} (h : a = b),
        HomologicalComplex.tensorHom
          (eqToIso (congrArg (tensorPowObj X) h)).hom (𝟙 X) =
        (eqToIso (congrArg
          (fun k => HomologicalComplex.tensorObj (tensorPowObj X k) X) h)).hom := by
      intro a b h
      cases h
      simp [HomologicalComplex.tensorHom_id_id]
    rw [← genX (Nat.add_assoc m n k)] at ⊢
    simp only [← CategoryTheory.Category.assoc,
      HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id] at ⊢
    have e1 : (𝟙 (tensorPowObj X m)) =
        𝟙 (tensorPowObj X m) ≫ 𝟙 (tensorPowObj X m) :=
      (CategoryTheory.Category.id_comp _).symm
    rw [e1] at ⊢
    rw [← HomologicalComplex.tensorHom_comp_tensorHom] at ⊢
    have hNat3MC := CategoryTheory.MonoidalCategory.associator_naturality
      (𝟙 (tensorPowObj X m)) (tensorPowObj_add X n k).hom (𝟙 X)
    have hNat3 : HomologicalComplex.tensorHom
          (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
            (tensorPowObj_add X n k).hom) (𝟙 X) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (HomologicalComplex.tensorObj (tensorPowObj X n)
            (tensorPowObj X k)) X).hom =
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X (n + k)) X).hom ≫
        HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (HomologicalComplex.tensorHom (tensorPowObj_add X n k).hom
            (𝟙 X)) := hNat3MC
    rw [CategoryTheory.Category.assoc _ _
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.tensorHom (tensorPowObj_add X n k).hom (𝟙 X)) ≫
      HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.associator (tensorPowObj X m)
        (tensorPowObj X (n + k)) X).hom
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.tensorHom (tensorPowObj_add X n k).hom (𝟙 X)))
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← hNat3] at ⊢
    rw [CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (tensorPowObj_add X n k).hom) (𝟙 X))
      (HomologicalComplex.associator (tensorPowObj X m)
        (HomologicalComplex.tensorObj (tensorPowObj X n)
          (tensorPowObj X k)) X).hom
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom
        ((eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom ≫
          (tensorPowObj_add X m (n + k)).hom) (𝟙 X))
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (tensorPowObj_add X n k).hom) (𝟙 X))
      ((HomologicalComplex.associator (tensorPowObj X m)
        (HomologicalComplex.tensorObj (tensorPowObj X n)
          (tensorPowObj X k)) X).hom ≫
      HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id] at ⊢
    rw [CategoryTheory.Category.assoc
      (eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom
      (tensorPowObj_add X m (n + k)).hom
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (tensorPowObj_add X n k).hom)] at ⊢
    rw [ih] at ⊢
    have e2 : (𝟙 X) = 𝟙 X ≫ 𝟙 X :=
      (CategoryTheory.Category.id_comp _).symm
    conv_lhs =>
      rw [e2, ← HomologicalComplex.tensorHom_comp_tensorHom]
    conv_lhs =>
      rw [e2, ← HomologicalComplex.tensorHom_comp_tensorHom,
        CategoryTheory.Category.comp_id]
    rw [CategoryTheory.Category.assoc] at ⊢
    rw [CategoryTheory.Category.assoc] at ⊢
    have hPentMC := CategoryTheory.MonoidalCategory.pentagon
      (tensorPowObj X m) (tensorPowObj X n) (tensorPowObj X k) X
    have hPent : HomologicalComplex.tensorHom
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X n) (tensorPowObj X k)).hom (𝟙 X) ≫
        ((HomologicalComplex.associator (tensorPowObj X m)
          (HomologicalComplex.tensorObj (tensorPowObj X n)
            (tensorPowObj X k)) X).hom ≫
        HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (HomologicalComplex.associator (tensorPowObj X n)
            (tensorPowObj X k) X).hom) =
        (HomologicalComplex.associator
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n)) (tensorPowObj X k) X).hom ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom := hPentMC
    rw [hPent] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
          (𝟙 (tensorPowObj X k))) (𝟙 X))
      (HomologicalComplex.associator
        (HomologicalComplex.tensorObj (tensorPowObj X m)
          (tensorPowObj X n)) (tensorPowObj X k) X).hom
      (HomologicalComplex.associator (tensorPowObj X m)
        (tensorPowObj X n)
        (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom] at ⊢
    have hNat9MC := CategoryTheory.MonoidalCategory.associator_naturality
      (tensorPowObj_add X m n).hom (𝟙 (tensorPowObj X k)) (𝟙 X)
    have hNat9 : HomologicalComplex.tensorHom
          (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
            (𝟙 (tensorPowObj X k))) (𝟙 X) ≫
        (HomologicalComplex.associator
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n)) (tensorPowObj X k) X).hom =
        (HomologicalComplex.associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom ≫
        HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
          (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X k))
            (𝟙 X)) := hNat9MC
    rw [hNat9] at ⊢
    rw [HomologicalComplex.tensorHom_id_id] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom (tensorPowObj_add X (m + n) k).hom
        (𝟙 X))
      ((HomologicalComplex.associator (tensorPowObj X (m + n))
        (tensorPowObj X k) X).hom ≫
      HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
        (𝟙 (HomologicalComplex.tensorObj (tensorPowObj X k) X)))
      (HomologicalComplex.associator (tensorPowObj X m)
        (tensorPowObj X n)
        (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom (tensorPowObj_add X (m + n) k).hom
        (𝟙 X))
      (HomologicalComplex.associator (tensorPowObj X (m + n))
        (tensorPowObj X k) X).hom
      (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
        (𝟙 (HomologicalComplex.tensorObj (tensorPowObj X k) X)))] at ⊢

-- Iterated tensor comparisons use the binary and iterated coproduct structures.
-- Unit comparisons use preservation of empty colimits by both tensor functors.
-- Associativity retains the left-associated finite tensor recursion.

/-- Equality of recursive and monoidal cochain tensor-power objects.

Under the graded coproduct, empty-colimit preservation and iterated tensor coherence
hypotheses giving the cochain monoidal structure, the recursive object P_n(X) equals the
general monoidal TensorPower.tensorPowObj X n. Both start at the same tensor unit and use Pₙ₊₁
= Pₙ ⊗ X. -/
theorem tensorPowObj_eq_tensorPower (X : CochainComplex (ModuleCat R) ℤ)
    (n : ℕ) :
    tensorPowObj X n =
      CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tensorPowObj_succ,
      CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_succ, ih]
    rfl

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)]
  [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- Tensor transport of an equality with a fixed right factor.

For an equality e : A = B of cochain complexes and fixed X, the canonical map induced by A ⊗ X
= B ⊗ X equals (eqToIso e).hom ⊗ id_X. This uses the binary graded tensor structures and
requires no associator comparison. -/
theorem tensorPowObj_whisker_right
    {X : CochainComplex (ModuleCat R) ℤ}
    {A B : CochainComplex (ModuleCat R) ℤ} (e : A = B) :
    (eqToIso (congrArg (fun Y => HomologicalComplex.tensorObj Y X) e)).hom =
      HomologicalComplex.tensorHom (eqToIso e).hom (𝟙 X) := by
  cases e
  simp [HomologicalComplex.tensorHom_id_id]

/-- Successor formula for the tensor-power object comparison.

Let B_n : P_n(X) ≅ Q_n(X) be the canonical isomorphism from equality of the recursive and
general monoidal power objects, under the cochain monoidal hypotheses. Its successor hom is
Bₙ₊₁.hom = Bₙ.hom ⊗ id_X. -/
theorem tensorPowObj_bridge_succ
    (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    (eqToIso (tensorPowObj_eq_tensorPower X (n + 1))).hom =
      HomologicalComplex.tensorHom
        (eqToIso (tensorPowObj_eq_tensorPower X n)).hom (𝟙 X) := by
  have hEq : tensorPowObj_eq_tensorPower X (n + 1) =
      congrArg (fun Y => HomologicalComplex.tensorObj Y X)
        (tensorPowObj_eq_tensorPower X n) := proof_irrel _ _
  rw [hEq]
  exact tensorPowObj_whisker_right (tensorPowObj_eq_tensorPower X n)

/-- Map equation for recursive and monoidal tensor powers.

Under the cochain monoidal hypotheses, let B_X,n : P_n(X) ≅ Q_n(X) be the canonical object
comparison. For g : X → Y, B_X,n.hom ≫ Q_n(g) = P_n(g) ≫ B_Y,n.hom. Both power maps follow the
same left-associated recursion. -/
theorem tensorPowObj_powMap_bridge
    {X Y : CochainComplex (ModuleCat R) ℤ} (g : X ⟶ Y) (n : ℕ) :
    (eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
        CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n =
      tensorPowMap g n ≫
        (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom := by
  induction n with
  | zero =>
      have hbX : (eqToIso (tensorPowObj_eq_tensorPower X 0)).hom =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have hbY : (eqToIso (tensorPowObj_eq_tensorPower Y 0)).hom =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have zG : CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g 0 =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have zD : tensorPowMap g 0 =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have cL : (eqToIso (tensorPowObj_eq_tensorPower X 0)).hom ≫
              CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g 0 =
            𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) := by
        rw [hbX, zG]
        exact Category.comp_id _
      have cR : 𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) =
            tensorPowMap g 0 ≫
              (eqToIso (tensorPowObj_eq_tensorPower Y 0)).hom := by
        rw [zD, hbY]
        exact (Category.id_comp _).symm
      exact cL.trans cR
  | succ n ih =>
      have hGen : CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g
            (n + 1) =
          HomologicalComplex.tensorHom
            (CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
            g := rfl
      have hDG : tensorPowMap g (n + 1) =
          HomologicalComplex.tensorHom (tensorPowMap g n) g :=
        tensorPowMap_succ g n
      have cL : (eqToIso (tensorPowObj_eq_tensorPower X (n + 1))).hom ≫
              CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g (n + 1) =
            HomologicalComplex.tensorHom
              ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
                CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
              (𝟙 X ≫ g) := by
        have e1 := congrArg (fun b => b ≫
          CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g (n + 1))
          (tensorPowObj_bridge_succ X n)
        have e2 := congrArg (fun m => HomologicalComplex.tensorHom
          (eqToIso (tensorPowObj_eq_tensorPower X n)).hom (𝟙 X) ≫ m) hGen
        have e3 : HomologicalComplex.tensorHom
                (eqToIso (tensorPowObj_eq_tensorPower X n)).hom (𝟙 X) ≫
                HomologicalComplex.tensorHom
                  (CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
                  g =
              HomologicalComplex.tensorHom
                ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
                  CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
                (𝟙 X ≫ g) :=
          HomologicalComplex.tensorHom_comp_tensorHom _ _ _ _
        exact e1.trans (e2.trans e3)
      have cM : HomologicalComplex.tensorHom
              ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
                CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
              (𝟙 X ≫ g) =
            HomologicalComplex.tensorHom
              (tensorPowMap g n ≫
                (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) g := by
        rw [ih, Category.id_comp]
      have cR : HomologicalComplex.tensorHom
              (tensorPowMap g n ≫
                (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) g =
            tensorPowMap g (n + 1) ≫
              (eqToIso (tensorPowObj_eq_tensorPower Y (n + 1))).hom := by
        have e0 : HomologicalComplex.tensorHom
                (tensorPowMap g n ≫
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) g =
              HomologicalComplex.tensorHom
                (tensorPowMap g n ≫
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom)
                (g ≫ 𝟙 Y) := by
          rw [Category.comp_id]
        have e1 : HomologicalComplex.tensorHom
                (tensorPowMap g n ≫
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom)
                (g ≫ 𝟙 Y) =
              HomologicalComplex.tensorHom (tensorPowMap g n) g ≫
                HomologicalComplex.tensorHom
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom (𝟙 Y) :=
          (HomologicalComplex.tensorHom_comp_tensorHom _ _ _ _).symm
        have e2 := congrArg (fun m => m ≫
          HomologicalComplex.tensorHom
            (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom (𝟙 Y)) hDG
        have e3 := congrArg (fun b => tensorPowMap g (n + 1) ≫ b)
          (tensorPowObj_bridge_succ Y n)
        exact e0.trans (e1.trans (e2.symm.trans e3.symm))
      exact cL.trans (cM.trans cR)

/-- Inverse comparison equation for tensor-power maps.

For g : X → Y and the canonical comparisons B_X,n : P_n(X) ≅ Q_n(X), the power maps satisfy
Q_n(g) ≫ B_Y,n.inv = B_X,n.inv ≫ P_n(g), under the cochain monoidal hypotheses. -/
theorem tensorPowObj_powMap_bridge_inv
    {X Y : CochainComplex (ModuleCat R) ℤ} (g : X ⟶ Y) (n : ℕ) :
    CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n ≫
        (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv =
      (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
        tensorPowMap g n := by
  have h := tensorPowObj_powMap_bridge g n
  calc CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n ≫
          (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv
      = (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
          ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
            (CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n ≫
              (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv)) := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
          ((tensorPowMap g n ≫
            (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) ≫
            (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv) := by
        rw [← Category.assoc ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom),
          h]
    _ = (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
          tensorPowMap g n := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

example (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    HomologicalComplex.HasTensor (tensorPowObj X n) X :=
  inferInstance

example (X : CochainComplex (ModuleCat R) ℤ) (m n : ℕ) :
    HomologicalComplex.HasGoodTensor₁₂
      (tensorPowObj X m) (tensorPowObj X n) X :=
  inferInstance

example (X : CochainComplex (ModuleCat R) ℤ) (m n : ℕ) :
    HomologicalComplex.HasGoodTensor₂₃
      (tensorPowObj X m) (tensorPowObj X n) X :=
  inferInstance

end AddCoherence

end CochainComplex

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).obj X)]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).flip.obj X)]
variable [∀ W X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasTensor₄ObjExt W X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensorTensor₂₃ X Y Z]

/-- Compatibility of recursive and monoidal block-splitting maps.

Let R : Type u and X be a cochain complex in ModuleCat.{u} R, with the stated cochain monoidal
hypotheses. Write B_n : P_n(X) ≅ Q_n(X) for the canonical object comparisons. Then
a^P_{m,n}.hom ≫ (B_m.hom ⊗ B_n.hom) = B_{m+n}.hom ≫ a^Q_{m,n}.hom for all m,n : ℕ. -/
theorem tensorPowObj_add_bridge_hom
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℕ) :
    (tensorPowObj_add X m n).hom ≫
      HomologicalComplex.tensorHom
        (eqToIso (tensorPowObj_eq_tensorPower X m)).hom
        (eqToIso (tensorPowObj_eq_tensorPower X n)).hom =
    (eqToIso (tensorPowObj_eq_tensorPower X (m + n))).hom ≫
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowAddIso X m n).hom := by
  induction n with
  | zero =>
    change (ρ_ (tensorPowObj X m)).inv ≫
        ((eqToIso (tensorPowObj_eq_tensorPower X m)).hom ⊗ₘ 𝟙 _) =
      (eqToIso (tensorPowObj_eq_tensorPower X m)).hom ≫
        (ρ_ (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X m)).inv
    exact (rightUnitor_inv_naturality (eqToIso (tensorPowObj_eq_tensorPower X m)).hom).symm
  | succ n ih =>
    let N := tensorPowObj_add X m n
    let A := CategoryTheory.MonoidalCategory.TensorPower.tensorPowAddIso X m n
    let Bm := eqToIso (tensorPowObj_eq_tensorPower X m)
    let Bn := eqToIso (tensorPowObj_eq_tensorPower X n)
    let Bsum := eqToIso (tensorPowObj_eq_tensorPower X (m + n))
    let αN := HomologicalComplex.associator (tensorPowObj X m) (tensorPowObj X n) X
    let αA := HomologicalComplex.associator
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X m)
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X n) X
    have hN : (tensorPowObj_add X m (n + 1)).hom =
        HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ αN.hom := by rfl
    have hA : (CategoryTheory.MonoidalCategory.TensorPower.tensorPowAddIso X m (n + 1)).hom =
        HomologicalComplex.tensorHom A.hom (𝟙 X) ≫ αA.hom := by rfl
    rw [hN, hA]
    simp only [tensorPowObj_bridge_succ]
    change (HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ αN.hom) ≫
        HomologicalComplex.tensorHom Bm.hom (HomologicalComplex.tensorHom Bn.hom (𝟙 X)) =
      HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
        (HomologicalComplex.tensorHom A.hom (𝟙 X) ≫ αA.hom)
    have hNat : αN.hom ≫
        HomologicalComplex.tensorHom Bm.hom (HomologicalComplex.tensorHom Bn.hom (𝟙 X)) =
      HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) ≫ αA.hom :=
      (associator_naturality Bm.hom Bn.hom (𝟙 X)).symm
    have hCompN : HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
        HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) =
      HomologicalComplex.tensorHom (N.hom ≫ HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) := by
      rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id]
    have hCompA : HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
        HomologicalComplex.tensorHom A.hom (𝟙 X) =
      HomologicalComplex.tensorHom (Bsum.hom ≫ A.hom) (𝟙 X) := by
      rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id]
    calc
      (HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ αN.hom) ≫
          HomologicalComplex.tensorHom Bm.hom (HomologicalComplex.tensorHom Bn.hom (𝟙 X)) =
        HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
          (αN.hom ≫ HomologicalComplex.tensorHom Bm.hom
            (HomologicalComplex.tensorHom Bn.hom (𝟙 X))) := Category.assoc _ _ _
      _ = HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
          (HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) ≫
            αA.hom) :=
        congrArg (fun f => HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ f) hNat
      _ = (HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
          HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X)) ≫
            αA.hom :=
        (Category.assoc _ _ _).symm
      _ = HomologicalComplex.tensorHom
          (N.hom ≫ HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) ≫ αA.hom :=
        congrArg (fun f => f ≫ αA.hom) hCompN
      _ = HomologicalComplex.tensorHom (Bsum.hom ≫ A.hom) (𝟙 X) ≫ αA.hom :=
        congrArg (fun f => HomologicalComplex.tensorHom f (𝟙 X) ≫ αA.hom) ih
      _ = (HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
          HomologicalComplex.tensorHom A.hom (𝟙 X)) ≫ αA.hom :=
        congrArg (fun f => f ≫ αA.hom) hCompA.symm
      _ = HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
          (HomologicalComplex.tensorHom A.hom (𝟙 X) ≫ αA.hom) := Category.assoc _ _ _

/-- Compatibility of recursive and monoidal block-concatenation maps.

For R : Type u and X in CochainComplex(ModuleCat.{u} R,ℤ), with the stated monoidal hypotheses
and object comparisons B_n, (B_m.hom ⊗ B_n.hom) ≫ a^Q_{m,n}.inv = a^P_{m,n}.inv ≫ B_{m+n}.hom.
The equality compares the inverse block-splitting maps without changing tensor order. -/
theorem tensorPowObj_add_bridge_inv
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℕ) :
    HomologicalComplex.tensorHom
        (eqToIso (tensorPowObj_eq_tensorPower X m)).hom
        (eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowAddIso X m n).inv =
    (tensorPowObj_add X m n).inv ≫
      (eqToIso (tensorPowObj_eq_tensorPower X (m + n))).hom := by
  let e := tensorPowObj_add X m n
  let f := CategoryTheory.MonoidalCategory.TensorPower.tensorPowAddIso X m n
  let a := HomologicalComplex.tensorHom
    (eqToIso (tensorPowObj_eq_tensorPower X m)).hom
    (eqToIso (tensorPowObj_eq_tensorPower X n)).hom
  let b := (eqToIso (tensorPowObj_eq_tensorPower X (m + n))).hom
  have h : e.hom ≫ a = b ≫ f.hom := tensorPowObj_add_bridge_hom X m n
  change a ≫ f.inv = e.inv ≫ b
  calc
    a ≫ f.inv = e.inv ≫ ((e.hom ≫ a) ≫ f.inv) := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = e.inv ≫ ((b ≫ f.hom) ≫ f.inv) := congrArg (fun k => e.inv ≫ (k ≫ f.inv)) h
    _ = e.inv ≫ b := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CochainComplex
