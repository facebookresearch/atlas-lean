/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
public import MathlibExt.Algebra.Homology.DGCyclicMixedModels
public import Mathlib.Data.Finsupp.Basic

/-!
# A source-normalized DG bar/cobar index for coherent module diagrams

An index generator is an actual strictly increasing object chain. Its
degree is minus the number of internal vertices. Its differential is
the alternating sum of deleting an internal vertex minus cutting there
and composing the two resulting generators. Formal words of generators
are a basis of every Hom degree. Thus a DG functor from this index
retains edge homotopies and every higher face, without demanding false
strict commutativity of native mapping-cone squares.

The joint module comparison below is a single closed map over the actual
index/category enveloping DG category. Its source is projectively
cofibrant there; pointwise cofibrancy does not replace that condition.

References: Bousfield--Kan, XII; the bar/cobar resolution of a linear
category; Brav--Dyckerhoff, arXiv:1606.00619v1, coherent diagrams 6.5--6.7.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGCoherentIndexModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels

universe u
variable {k : Type u} [Field k] {J : Type u} [PartialOrder J]

/-- An actual normalized index chain with m internal vertices. -/
structure Generator (J : Type u) [PartialOrder J] (a b : J) (m : ℕ) where
  vertices : Fin (m + 2) → J
  strict : StrictMono vertices
  first : vertices 0 = a
  last : vertices (Fin.last (m + 1)) = b

/-- Deleting the selected internal vertex is the actual category face. -/
def Generator.face {a b : J} {m : ℕ} (g : Generator J a b (m + 1)) (i : Fin (m + 1)) :
    Generator J a b m where
  vertices := g.vertices ∘ (Fin.succAboveOrderEmb i.castSucc.succ)
  strict := g.strict.comp (Fin.succAboveOrderEmb i.castSucc.succ).strictMono
  first := by
    change g.vertices (i.castSucc.succ.succAbove 0) = a
    simpa only [Fin.succ_succAbove_zero] using g.first
  last := by
    change g.vertices (i.castSucc.succ.succAbove (Fin.last (m + 1))) = b
    rw [Fin.succAbove_ne_last_last]
    · exact g.last
    · apply Fin.ne_of_lt
      change i.val + 1 < m + 2
      omega

def Generator.cutVertex {a b : J} {m : ℕ} (g : Generator J a b (m + 1)) (i : Fin (m + 1)) : J :=
  g.vertices ⟨i.val + 1, by omega⟩

/-- The prefix at a cut retains the original literal vertices. -/
def Generator.prefix {a b : J} {m : ℕ} (g : Generator J a b (m + 1)) (i : Fin (m + 1)) :
    Generator J a (g.cutVertex i) i.val where
  vertices j := g.vertices ⟨j.val, by omega⟩
  strict := by intro x y h; apply g.strict; exact h
  first := g.first
  last := rfl

/-- The suffix at the same cut uses the original literal vertices. -/
def Generator.suffix {a b : J} {m : ℕ} (g : Generator J a b (m + 1)) (i : Fin (m + 1)) :
    Generator J (g.cutVertex i) b (m - i.val) where
  vertices j := g.vertices ⟨j.val + i.val + 1, by omega⟩
  strict := by intro x y h; apply g.strict; change x.val + i.val + 1 < y.val + i.val + 1; omega
  first := by simp [Generator.cutVertex]
  last := by
    convert g.last using 1
    congr 1
    apply Fin.ext
    simp
    omega

/-- A genuine composable word of actual chain generators. -/
inductive Word (J : Type u) [PartialOrder J] : J → J → Type u
  | nil (a : J) : Word J a a
  | cons {a b c : J} {m : ℕ} (g : Generator J a b m) (w : Word J b c) : Word J a c

def Word.degree {a b : J} : Word J a b → ℤ
  | .nil _ => 0
  | .cons (m := m) _ w => -(m : ℤ) + w.degree

/-- Each degree is the native free k-module on actual composable words of that degree. -/
abbrev HomValues (a b : J) (r : ℤ) := {w : Word J a b // w.degree = r} →₀ k

/-- Native enriched word composition fixes the actual value of every formal generator word. -/
def wordElement (C : DGCat k) (objects : C ≃ J)
    (cell : ∀ {a b : J} {m : ℕ}, Generator J a b m →
      DGHom k (-(m : ℤ)) (objects.symm a) (objects.symm b))
    {a b : J} (w : Word J a b) : DGHom k w.degree (objects.symm a) (objects.symm b) :=
  match w with
  | .nil a => dgId k (objects.symm a)
  | .cons g w => dgComp k (cell g) (wordElement C objects cell w) rfl

/-- The actual DG bar/cobar index has all Hom words, products and chain faces fixed. -/
structure CoherentIndexModel (k : Type u) [Field k] (J : Type u) [PartialOrder J] where
  category : DGCat k
  objects : category ≃ J
  cell : ∀ {a b : J} {m : ℕ}, Generator J a b m →
    DGHom k (-(m : ℤ)) (objects.symm a) (objects.symm b)
  termIso : ∀ (a b : J) (r : ℤ),
    (dgHomComplex k (objects.symm a) (objects.symm b)).X r ≅ ModuleCat.of k (HomValues (k := k) a b r)
  word_eq : ∀ {a b : J} (w : Word J a b),
    (termIso a b w.degree).hom (wordElement category objects cell w) = Finsupp.single ⟨w, rfl⟩ 1
  closed_arrow : ∀ {a b : J} (g : Generator J a b 0), dgDifferential k 0 (cell g) = 0
  cell_boundary : ∀ {a b : J} {m : ℕ} (g : Generator J a b (m + 1)),
    dgDifferential k (-((m + 1 : ℕ) : ℤ)) (cell g) =
      ∑ i : Fin (m + 1), (-1 : ℤ) ^ i.val •
        (degreeCast (dgHomComplex k (objects.symm a) (objects.symm b)) (by omega)
          (cell (g.face i)) -
        dgComp k (cell (g.prefix i)) (cell (g.suffix i)) (by omega))

/-- One actual coherent diagram, retaining all DG arrows and their higher cells. -/
abbrev CoherentDiagram (R : CoherentIndexModel k J) (C : DGCat k) := Bimodule k R.category C

/-- A whole projective comparison is one native map over the actual index/category tensor.
The uncurrying and its augmentation fix both index and coefficient actions in every degree. -/
structure JointProjectiveComparison (R : CoherentIndexModel k J) (C : DGCat k)
    (D E : CoherentDiagram R C) where
  source : EnvelopingModuleModel D
  target : EnvelopingModuleModel E
  replacement : ModuleReplacement source.module
  map : replacement.module ⟶ target.module

/-- The curried form of the same single comparison retains native naturality for every index word. -/
structure CurriedJointComparison (R : CoherentIndexModel k J) (C : DGCat k)
    (D E : CoherentDiagram R C) where
  replacement : CoherentDiagram R C
  sourceModel : EnvelopingModuleModel D
  replacementModel : EnvelopingModuleModel replacement
  targetModel : EnvelopingModuleModel E
  augmentation : replacement ⟶ D
  map : replacement ⟶ E
  uncurriedAugmentation : replacementModel.module ⟶ sourceModel.module
  uncurriedMap : replacementModel.module ⟶ targetModel.module
  augmentation_eq : ∀ (a : J) (x : Cᵒᵖ) (r : ℤ),
    HEq ((moduleComponent uncurriedAugmentation (moduleIndex R.category C (R.objects.symm a) x)).f r)
      ((moduleComponent (MathlibExt.CategoryTheory.DGMoritaClosedModels.columnMap augmentation
        (R.objects.symm a)) x).f r)
  map_eq : ∀ (a : J) (x : Cᵒᵖ) (r : ℤ),
    HEq ((moduleComponent uncurriedMap (moduleIndex R.category C (R.objects.symm a) x)).f r)
      ((moduleComponent (MathlibExt.CategoryTheory.DGMoritaClosedModels.columnMap map
        (R.objects.symm a)) x).f r)
  cofibrant : IsCofibrantModule replacementModel.module
  trivial : IsModuleTrivialFibration uncurriedAugmentation

end MathlibExt.CategoryTheory.DGCoherentIndexModels
