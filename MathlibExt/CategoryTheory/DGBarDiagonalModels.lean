/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DGCategoryTraceModels
public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels

/-!
# Actual bar-diagonal resolutions and scalar free DG modules

Every diagonal bar term is a coproduct of the actual path Hom tensor
words. All boundary maps compose one adjacent pair through the native
enriched composition. The total differential and augmentation are fixed
on those same paths.

Scalar free modules have the native pointwise cochain tensor values and
the signed action on every homogeneous pure tensor. The diagonal bar
action is fixed on the shifted free representable summands, retaining
the (-1)^(n p) action sign of bar-degree n. Its projective replacement
and all module-arrow data are construction outputs, without any CY class.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, §§2.1--2.3;
Keller, Deriving DG categories, §§2--3. Native tensor/representable
proofs retain their original attribution in DGSource.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGBarDiagonalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.MonoidalTensorWordModels
open MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [CommRing k]

/-- A native homogeneous cochain tensor generator at its actual total degree. -/
def tensorElement (K L : Cochains k) {i j r : ℤ} (h : i + j = r)
    (a : K.X i) (b : L.X j) : (K ⊗ L).X r :=
  (HomologicalComplex.ιTensorObj K L i j r h).hom (TensorProduct.tmul k a b)

/-- The actual pointwise scalar tensor module, normalized on every homogeneous generator. -/
structure ScalarTensorModuleModel {C : DGCat k} (K : Cochains k) (R : RightModule k C) where
  module : RightModule k C
  valueIso : ∀ x : Cᵒᵖ, module.toEnrichedFunctor.obj x ≅ K ⊗ R.toEnrichedFunctor.obj x
  action : ∀ (x y : Cᵒᵖ) (p i j r s : ℤ) (h : i + j = r) (hs : r + p = s)
    (a : DGHom k p x y) (m : K.X i) (v : (R.toEnrichedFunctor.obj x).X j),
    ((valueIso y).hom.f s)
      (((module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r s hs)
        (((valueIso x).inv.f r) (tensorElement K (R.toEnrichedFunctor.obj x) h m v))) =
      (p * i).negOnePow • tensorElement K (R.toEnrichedFunctor.obj y)
        (i := i) (j := j + p) (r := s) (by omega)
        m (((R.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v j (j + p) rfl) v)

/-- The intermediate vertices in the actual n-th two-sided bar path. -/
abbrev PathVertices (C : DGCat k) (n : ℕ) := {xs : List C // xs.length = n + 1}

/-- Remove any one intermediate vertex by the actual adjacent DG composition. -/
def contractVertex (C : DGCat k) (a : C) :
    (xs : List C) → (i : Fin xs.length) → (b : C) →
      (pathTensor C a xs b ⟶ pathTensor C a (xs.eraseIdx i.val) b)
  | [], i, _ => Fin.elim0 i
  | y :: ys, i, b => Fin.cases
      (contractFirst C a y ys b)
      (fun j => 𝟙 (dgHomComplex k a y) ⊗ₘ contractVertex C y ys j b) i

/-- The actual path word in bar degree n at the indicated bimodule pair. -/
def diagonalBarTerm (C : DGCat k) (n : ℕ) (x : C) (y : Cᵒᵖ) : Cochains k :=
  ∐ fun v : PathVertices C n => pathTensor C y.unop v.val x

/-- Deleting an intermediate vertex has precisely the next bar arity. -/
def deletedVertices (C : DGCat k) (n : ℕ) (v : PathVertices C (n + 1))
    (i : Fin (n + 2)) : PathVertices C n :=
  ⟨v.val.eraseIdx i.val, by
    rw [List.length_eraseIdx_of_lt (by rw [v.property]; exact i.isLt), v.property]
    omega⟩

/-- Every two-sided bar face is fixed by the adjacent-composition word contraction. -/
def diagonalBarFace (C : DGCat k) (n : ℕ) (x : C) (y : Cᵒᵖ) (i : Fin (n + 2)) :
    diagonalBarTerm C (n + 1) x y ⟶ diagonalBarTerm C n x y :=
  Sigma.desc (fun v =>
    contractVertex C y.unop v.val (Fin.cast v.property.symm i) x ≫
      Sigma.ι (fun w : PathVertices C n => pathTensor C y.unop w.val x)
        (deletedVertices C n v i))

/-- The source direct-sum total term has all intermediate-object paths. -/
abbrev DiagonalValues (C : DGCat k) (x : C) (y : Cᵒᵖ) (r : ℤ) :=
  DirectSum ℕ (fun n => ↥((diagonalBarTerm C n x y).X (r + (n : ℤ))))

/-- Native inclusion of the same bar-degree path term. -/
def includeDiagonal (C : DGCat k) (x : C) (y : Cᵒᵖ) (r : ℤ) (n : ℕ) :
    (diagonalBarTerm C n x y).X (r + (n : ℤ)) →ₗ[k] DiagonalValues C x y r :=
  DirectSum.lof k ℕ (fun n => ↥((diagonalBarTerm C n x y).X (r + (n : ℤ)))) n

/-- The actual internal differential of a diagonal bar term. -/
def diagonalInternalBlock (C : DGCat k) (x : C) (y : Cᵒᵖ) (r : ℤ) (n : ℕ) :
    (diagonalBarTerm C n x y).X (r + (n : ℤ)) →ₗ[k] DiagonalValues C x y (r + 1) :=
  (includeDiagonal C x y (r + 1) n).comp
    ((degreeCast (diagonalBarTerm C n x y) (by omega)).comp
      ((diagonalBarTerm C n x y).d (r + (n : ℤ)) (r + (n : ℤ) + 1)).hom)

/-- The actual alternating diagonal path faces. -/
def diagonalFaceBlock (C : DGCat k) (x : C) (y : Cᵒᵖ) (r : ℤ) : (n : ℕ) →
    ((diagonalBarTerm C n x y).X (r + (n : ℤ)) →ₗ[k] DiagonalValues C x y (r + 1))
  | 0 => 0
  | n + 1 => (includeDiagonal C x y (r + 1) n).comp
      ((degreeCast (diagonalBarTerm C n x y) (by omega)).comp
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          ((diagonalBarFace C n x y i).f (r + ((n + 1 : ℕ) : ℤ))).hom))

/-- The complete two-sided bar total differential on every actual path summand. -/
def diagonalDifferential (C : DGCat k) (x : C) (y : Cᵒᵖ) (r : ℤ) :
    DiagonalValues C x y r →ₗ[k] DiagonalValues C x y (r + 1) :=
  DirectSum.toModule k ℕ (DiagonalValues C x y (r + 1))
    (fun n => (-1 : ℤ) ^ n • diagonalInternalBlock C x y r n + diagonalFaceBlock C x y r n)

/-- The augmentation of one degree-zero path is the actual two-factor DG composition. -/
def diagonalAugmentationWord (C : DGCat k) (x : C) (y : Cᵒᵖ)
    (v : PathVertices C 0) : pathTensor C y.unop v.val x ⟶ dgHomComplex k y.unop x := by
  rcases v with ⟨xs, h⟩
  cases xs with
  | nil => simp at h
  | cons z zs =>
    have hz : zs = [] := by simpa using h
    subst hz
    exact contractFirst C y.unop z [] x ≫ (ρ_ (dgHomComplex k y.unop x)).hom

/-- The actual degree-zero path augmentation on its coproduct. -/
def diagonalAugmentationBar (C : DGCat k) (x : C) (y : Cᵒᵖ) :
    diagonalBarTerm C 0 x y ⟶ dgHomComplex k y.unop x :=
  Sigma.desc (diagonalAugmentationWord C x y)

/-- The total augmentation composes degree-zero paths and kills positive bar degrees. -/
def diagonalAugmentation (C : DGCat k) (x : C) (y : Cᵒᵖ) (r : ℤ) :
    DiagonalValues C x y r →ₗ[k] (dgHomComplex k y.unop x).X r :=
  DirectSum.toModule k ℕ ((dgHomComplex k y.unop x).X r)
    (fun n => match n with
      | 0 => ((diagonalAugmentationBar C x y).f r).hom.comp
          (degreeCast (diagonalBarTerm C 0 x y) (by omega))
      | _ + 1 => 0)

/-- The path's intermediate adjacent Hom factors, excluding its outer endpoint factors. -/
def middleFactors (C : DGCat k) (a : C) : List C → List (Cochains k)
  | [] => []
  | z :: zs => dgHomComplex k a z :: middleFactors C z zs

/-- The actual terminal object of an object path. -/
def endObject (C : DGCat k) (a : C) : List C → C
  | [] => a
  | z :: zs => endObject C z zs

/-- The complete path factors split after the literal intermediate word. -/
theorem pathFactors_eq_middle (C : DGCat k) (a b : C) (xs : List C) :
    pathFactors C a xs b = middleFactors C a xs ++ [dgHomComplex k (endObject C a xs) b] := by
  induction xs generalizing a with
  | nil => rfl
  | cons z zs ih => simp only [pathFactors, middleFactors, endObject, ih, List.cons_append]

/-- A bar path contains at least its first intermediate object. -/
theorem pathVertices_ne_nil {C : DGCat k} {n : ℕ} (v : PathVertices C n) : v.val ≠ [] := by
  intro h
  have hv := v.property
  rw [h] at hv
  simp at hv

/-- The literal first intermediate object. -/
def pathRoot {C : DGCat k} {n : ℕ} (v : PathVertices C n) : C :=
  v.val.head (pathVertices_ne_nil v)

/-- The native cochain word of all intermediate Hom factors. -/
def middleComplex {C : DGCat k} {n : ℕ} (v : PathVertices C n) : Cochains k :=
  word (middleFactors C (pathRoot v) v.val.tail)

/-- The actual enveloping representable for the path's two outer endpoints. -/
def pathRepresentable {C : DGCat k} {n : ℕ} (v : PathVertices C n) :
    RightModule k (enveloping C C) :=
  (dgYoneda k (C := enveloping C C)).obj
    (op (endObject C (pathRoot v) v.val.tail), pathRoot v)

/-- Native braiding and reassociation identify the free representable tensor with its path word. -/
def freePathTensorIso {C : DGCat k} {n : ℕ} (v : PathVertices C n) (x : C) (y : Cᵒᵖ) :
    middleComplex v ⊗ (pathRepresentable v).toEnrichedFunctor.obj (moduleIndex C C x y) ≅
      pathTensor C y.unop v.val x := by
  let K := middleComplex v
  let L := dgHomComplex k (endObject C (pathRoot v) v.val.tail) x
  let F := dgHomComplex k y.unop (pathRoot v)
  have hpath : pathTensor C y.unop v.val x =
      word (F :: (middleFactors C (pathRoot v) v.val.tail ++ [L])) := by
    unfold pathTensor
    congr 1
    calc
      pathFactors C y.unop v.val x =
          pathFactors C y.unop (pathRoot v :: v.val.tail) x := by
        rw [pathRoot, List.cons_head_tail]
      _ = _ := by simp only [pathFactors, pathFactors_eq_middle]; rfl
  exact eqToIso (show middleComplex v ⊗
      (pathRepresentable v).toEnrichedFunctor.obj (moduleIndex C C x y) = K ⊗ (L ⊗ F) from rfl) ≪≫
    (α_ K L F).symm ≪≫ β_ (K ⊗ L) F ≪≫
      tensorIso (Iso.refl F)
        (tensorIso (Iso.refl K) (ρ_ L).symm ≪≫
          (appendIso (middleFactors C (pathRoot v) v.val.tail) [L]).symm) ≪≫
      eqToIso hpath.symm

/-- Each bar path is the actual scalar tensor of its native enveloping representable. -/
structure FreeDiagonalSystem (C : DGCat k) where
  free : ∀ (n : ℕ) (v : PathVertices C n),
    ScalarTensorModuleModel (middleComplex v) (pathRepresentable v)

/-- The same source free module is identified with the actual path word in every pair. -/
def freeToPathIso {C : DGCat k} (F : FreeDiagonalSystem C) (n : ℕ) (v : PathVertices C n)
    (x : C) (y : Cᵒᵖ) :
    (F.free n v).module.toEnrichedFunctor.obj (moduleIndex C C x y) ≅
      pathTensor C y.unop v.val x :=
  (F.free n v).valueIso (moduleIndex C C x y) ≪≫ freePathTensorIso v x y

/-- Native inclusion of the fixed free representable's coefficient into the total bar. -/
def includeFreeDiagonal {C : DGCat k} (F : FreeDiagonalSystem C) (n : ℕ)
    (v : PathVertices C n) (x : C) (y : Cᵒᵖ) (r : ℤ) :
    ((F.free n v).module.toEnrichedFunctor.obj (moduleIndex C C x y)).X (r + (n : ℤ)) →ₗ[k]
      DiagonalValues C x y r :=
  (includeDiagonal C x y r n).comp
    (((Sigma.ι (fun w : PathVertices C n => pathTensor C y.unop w.val x) v).f
      (r + (n : ℤ))).hom.comp (((freeToPathIso F n v x y).hom.f (r + (n : ℤ))).hom))

/-- The diagonal's value is fixed by the actual identity graph and module uncurrying. -/
def diagonalValueIso {C : DGCat k} (D : EnvelopingModuleModel (diagonal C))
    (x : C) (y : Cᵒᵖ) :
    D.module.toEnrichedFunctor.obj (moduleIndex C C x y) ≅ dgHomComplex k y.unop x :=
  eqToIso (by rw [D.value_eq]; rfl)

/-- A genuine diagonal bar resolution has every value, differential, augmentation and module action fixed. -/
structure BarDiagonalModel {C : DGCat k} (D : EnvelopingModuleModel (diagonal C))
    (F : FreeDiagonalSystem C) where
  module : RightModule k (enveloping C C)
  augmentation : module ⟶ D.module
  cofibrant : IsCofibrantModule module
  trivialFibration : IsModuleTrivialFibration augmentation
  termIso : ∀ (x : C) (y : Cᵒᵖ) (r : ℤ),
    (module.toEnrichedFunctor.obj (moduleIndex C C x y)).X r ≅ ModuleCat.of k (DiagonalValues C x y r)
  differential_eq : ∀ (x : C) (y : Cᵒᵖ) (r : ℤ),
    (module.toEnrichedFunctor.obj (moduleIndex C C x y)).d r (r + 1) ≫
      (termIso x y (r + 1)).hom =
      (termIso x y r).hom ≫ ModuleCat.ofHom (diagonalDifferential C x y r)
  augmentation_eq : ∀ (x : C) (y : Cᵒᵖ) (r : ℤ),
    (moduleComponent augmentation (moduleIndex C C x y)).f r ≫
      (diagonalValueIso D x y).hom.f r =
      (termIso x y r).hom ≫ ModuleCat.ofHom (diagonalAugmentation C x y r)
  action_eq : ∀ (x x' : C) (y y' : Cᵒᵖ) (p r : ℤ) (n : ℕ) (v : PathVertices C n)
    (a : DGHom k p (moduleIndex C C x y) (moduleIndex C C x' y'))
    (z : ((F.free n v).module.toEnrichedFunctor.obj (moduleIndex C C x y)).X (r + (n : ℤ))),
    ((termIso x' y' (r + p)).hom)
      (((module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r (r + p) rfl)
        ((termIso x y r).inv (includeFreeDiagonal F n v x y r z))) =
      ((n : ℤ) * p).negOnePow • includeFreeDiagonal F n v x' y' (r + p)
        (((F.free n v).module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v
          (r + (n : ℤ)) (r + p + (n : ℤ)) (by omega) z)

/-- This normalized bar is the actual projective diagonal replacement used by duality. -/
def BarDiagonalModel.toReplacement {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} (P : BarDiagonalModel D F) : CofibrantDiagonal D where
  module := P.module
  augmentation := P.augmentation
  cofibrant := P.cofibrant
  trivialFibration := P.trivialFibration

end MathlibExt.CategoryTheory.DGBarDiagonalModels
