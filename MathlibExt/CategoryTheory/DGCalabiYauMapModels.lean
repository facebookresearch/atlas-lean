/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGBarDiagonalModels
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Actual inverse dualizing modules and negative-cyclic class maps

The inverse dualizing value is the actual enriched Hom from the
projective bar diagonal to the swapped enveloping representable.
Its action is native Yoneda/postcomposition after the cochain braiding
which swaps the two enveloping factors. A projective replacement retains
the full enveloping action before derived Hom is formed.

The trace comparison is fixed on every cyclic Hom tensor generator by
evaluation on the bar diagonal path obtained by appending the identity of the
distinguished object, followed by actual DG composition. The class map has degree -n in the actual bimodule Hom
complex, and its point maps land in the actual shifted diagonal. Left CY
nondegeneracy is a separate predicate on these fixed maps.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, §2.3,
equation3.4 and Definition3.5. This is the left dual A!→A[-n]; the
proper/right-CY dual A* and ordinary cyclic direction are distinct.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGCalabiYauMapModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [Field k]

/-- The opposite enveloping arrow acts on the swapped representable by native cochain braiding. -/
def inverseDualIndexHom (C : DGCat k) (x x' : C) (y y' : Cᵒᵖ) :
    dgHomComplex k (moduleIndex C C x y) (moduleIndex C C x' y') ⟶
      dgHomComplex k ((op y.unop, x) : enveloping C C)
        ((op y'.unop, x') : enveloping C C) :=
  (β_ (dgHomComplex k x x') (dgHomComplex k y y')).hom

/-- The actual inverse-dualizing action is Yoneda followed by native enriched postcomposition. -/
def inverseDualAction {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} (P : BarDiagonalModel D F)
    (x x' : C) (y y' : Cᵒᵖ) (p : ℤ)
    (a : DGHom k p (moduleIndex C C x y) (moduleIndex C C x' y')) :
    Cochain (inverseDualizingValue P.toReplacement x y)
      (inverseDualizingValue P.toReplacement x' y') p :=
  (cochainCorepresentable P.module).dgMap p
    ((dgYoneda k (C := enveloping C C)).dgMap p ((inverseDualIndexHom C x x' y y').f p a))

/-- The full inverse dualizing module has all values and every enveloping arrow fixed. -/
structure InverseDualModel {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} (P : BarDiagonalModel D F) where
  module : RightModule k (enveloping C C)
  valueIso : ∀ (x : C) (y : Cᵒᵖ),
    module.toEnrichedFunctor.obj (moduleIndex C C x y) ≅ inverseDualizingValue P.toReplacement x y
  action_eq : ∀ (x x' : C) (y y' : Cᵒᵖ) (p r s : ℤ) (h : r + p = s)
    (a : DGHom k p (moduleIndex C C x y) (moduleIndex C C x' y'))
    (v : (module.toEnrichedFunctor.obj (moduleIndex C C x y)).X r),
    ((valueIso x' y').hom.f s)
      (((module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r s h) v) =
      (inverseDualAction P x x' y y' p a).v r s h (((valueIso x y).hom.f r) v)
  replacement : ModuleReplacement module

/-- The two-sided bar path of a trace object cycle: the cyclic word followed by the identity of
the distinguished object. The first Hom factor of the cyclic word (the Hochschild coefficient) is
the left outer factor of the path, the remaining factors are its bar entries, and the appended
identity is its right outer factor. With this placement deleting the `i`-th intermediate vertex of
the inserted path gives the inserted path of the `i`-th cyclic face for every `i < n`. The last bar
face leaves the vertex list of the closing cyclic face, rooted at the last tail object; it agrees
with that face only after the trace pairing moves the outer coefficient around, not as a literal
based path. -/
def tracePathVertices {C : DGCat k} {n : ℕ} (s : CyclicObjects C n) : PathVertices C n :=
  ⟨List.ofFn s.tail ++ [s.root], by simp⟩

/-- Native unit insertion maps the cyclic word into the corresponding diagonal bar path by
appending the identity of the distinguished object as the last factor. -/
def traceBarInsertion (C : DGCat k) (n : ℕ) (s : CyclicObjects C n) :
    cycleTensor C s ⟶ diagonalBarTerm C n s.root (op s.root) :=
  (ρ_ (cycleTensor C s)).inv ≫
    (𝟙 (cycleTensor C s) ⊗ₘ (eId (Cochains k) s.root ≫ (ρ_ (dgHomComplex k s.root s.root)).inv)) ≫
    (MathlibExt.CategoryTheory.MonoidalTensorWordModels.appendIso
      (pathFactors C s.root (List.ofFn s.tail) s.root) [dgHomComplex k s.root s.root]).inv ≫
    eqToHom (by
      simp only [pathTensor, tracePathVertices]
      rw [pathFactors_append_last]) ≫
    Sigma.ι (fun v : PathVertices C n => pathTensor C s.root v.val s.root) (tracePathVertices s)

/-- The inserted cyclic generator is evaluated in the actual projective diagonal value. -/
def insertedCycle {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} (P : BarDiagonalModel D F) (n : ℕ)
    (s : CyclicObjects C n) (r : ℤ) (v : (cycleTensor C s).X (r + (n : ℤ))) :
    (P.module.toEnrichedFunctor.obj (moduleIndex C C s.root (op s.root))).X r :=
  (P.termIso s.root (op s.root) r).inv
    (includeDiagonal C s.root (op s.root) r n (((traceBarInsertion C n s).f (r + (n : ℤ))) v))

/-- The actual enclosing-representable value composes its two DG Hom factors. -/
def composeRepresentable (C : DGCat k) (x : C) (y : Cᵒᵖ) (z : C) :
    ((dgYoneda k (C := enveloping C C)).obj (op y.unop, x)).toEnrichedFunctor.obj
      (moduleIndex C C z (op z)) ⟶ dgHomComplex k y.unop x :=
  eComp (Cochains k) y.unop z x

/-- Native trace inclusion of one actual cyclic Hom tensor into the chosen total. -/
def traceGenerator {C : DGCat k} (T : TraceMixedModel C) (n : ℕ)
    (s : CyclicObjects C n) (r : ℤ) (v : (cycleTensor C s).X (r + (n : ℤ))) : T.total.complex.X r :=
  (T.total.termIso r).inv
    (includeTrace C r n (((Sigma.ι (fun t : CyclicObjects C n => cycleTensor C t) s).f
      (r + (n : ℤ))) v))

/-- The actual bar-evaluation expression on every inverse-dualizing element. -/
def traceEvaluationValue {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} (P : BarDiagonalModel D F) (I : InverseDualModel P)
    (n : ℕ) (s : CyclicObjects C n) (x : C) (y : Cᵒᵖ) (r p : ℤ)
    (v : (cycleTensor C s).X (r + (n : ℤ)))
    (q : (I.replacement.module.toEnrichedFunctor.obj (moduleIndex C C x y)).X p) :
    (dgHomComplex k y.unop x).X (p + r) :=
  (r * p).negOnePow • degreeCast (dgHomComplex k y.unop x) (by omega)
    (((composeRepresentable C x y s.root).f (r + p))
      ((DGFunctor.dgApp k p (moduleIndex C C s.root (op s.root))
        (((I.valueIso x y).hom.f p)
          (((moduleComponent I.replacement.augmentation (moduleIndex C C x y)).f p) q)) :
          Cochain _ _ p).v r (r + p) rfl (insertedCycle P n s r v)))

/-- The class-to-bimodule map is fixed by actual bar-diagonal evaluation on all generators.
The cochain lift targets the same projective diagonal; its augmentation is normalized. -/
structure TraceEvaluationModel {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} (P : BarDiagonalModel D F) (I : InverseDualModel P)
    (T : TraceMixedModel C) where
  comparison : T.total.complex ⟶ dgHomComplex k I.replacement.module P.module
  normalized : ∀ (n : ℕ) (s : CyclicObjects C n) (x : C) (y : Cᵒᵖ) (r p : ℤ)
    (v : (cycleTensor C s).X (r + (n : ℤ)))
    (q : (I.replacement.module.toEnrichedFunctor.obj (moduleIndex C C x y)).X p),
    ((diagonalValueIso D x y).hom.f (p + r))
      (((moduleComponent P.augmentation (moduleIndex C C x y)).f (p + r))
        ((DGFunctor.dgApp k r (moduleIndex C C x y)
          ((comparison.f r) (traceGenerator T n s r v)) : Cochain _ _ r).v p (p + r) rfl q)) =
      traceEvaluationValue P I n s x y r p v q

/-- The source class has its literal cochain map k[n]→CC(A)[[u]]. -/
abbrev NegativeCYClass {C : DGCat k} {T : TraceMixedModel C} (N : NegativeTraceModel T) (n : ℤ) :=
  (𝟙_ (Cochains k))⟦n⟧ ⟶ N.complex

/-- The scalar in the actual shifted coefficient unit is recovered by the native shift iso. -/
def shiftedUnitScalar (k : Type u) [CommRing k] (n : ℤ)
    (a : ((𝟙_ (Cochains k))⟦n⟧).X (-n)) : k :=
  (((𝟙_ (Cochains k)).shiftFunctorObjXIso n (-n) 0 (by omega)).hom) a

/-- A negative-cyclic class induces the actual degree -n map A!→A[-n].
All shifted component maps are fixed by that same bimodule cochain. -/
structure LeftCYMapModel {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} {P : BarDiagonalModel D F} {I : InverseDualModel P}
    {T : TraceMixedModel C} (E : TraceEvaluationModel P I T)
    {N : NegativeTraceModel T} (R : NegativeProjectionModel N) (n : ℤ) (a : NegativeCYClass N n) where
  hom : DGHom k (-n) I.replacement.module P.module
  closed : dgDifferential k (-n) hom = 0
  normalized : ∀ u : ((𝟙_ (Cochains k))⟦n⟧).X (-n),
    ((a ≫ R.map ≫ E.comparison).f (-n)) u = shiftedUnitScalar k n u • hom
  component : ∀ (x : C) (y : Cᵒᵖ),
    I.replacement.module.toEnrichedFunctor.obj (moduleIndex C C x y) ⟶
      (P.module.toEnrichedFunctor.obj (moduleIndex C C x y))⟦-n⟧
  component_eq : ∀ (x : C) (y : Cᵒᵖ) (r : ℤ),
    (component x y).f r ≫
      ((P.module.toEnrichedFunctor.obj (moduleIndex C C x y)).shiftFunctorObjXIso
        (-n) r (r - n) (by omega)).hom =
      (DGFunctor.dgApp k (-n) (moduleIndex C C x y) hom : Cochain _ _ (-n)).v r (r - n) (by omega)

/-- Nondegeneracy tests the actual induced bimodule maps in every pair. -/
def IsLeftCYNondegenerate {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} {P : BarDiagonalModel D F} {I : InverseDualModel P}
    {T : TraceMixedModel C} {E : TraceEvaluationModel P I T}
    {N : NegativeTraceModel T} {R : NegativeProjectionModel N} {n : ℤ}
    {a : NegativeCYClass N n} (M : LeftCYMapModel E R n a) : Prop :=
  ∀ (x : C) (y : Cᵒᵖ), QuasiIso (M.component x y)

/-- The source left CY condition retains both homological smoothness and the induced-map test. -/
def IsLeftCalabiYau {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} {P : BarDiagonalModel D F} {I : InverseDualModel P}
    {T : TraceMixedModel C} {E : TraceEvaluationModel P I T}
    {N : NegativeTraceModel T} {R : NegativeProjectionModel N} {n : ℤ}
    {a : NegativeCYClass N n} (M : LeftCYMapModel E R n a) : Prop :=
  IsHomologicallySmooth C D ∧ IsLeftCYNondegenerate M

end MathlibExt.CategoryTheory.DGCalabiYauMapModels
