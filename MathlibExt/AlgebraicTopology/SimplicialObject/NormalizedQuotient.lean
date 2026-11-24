/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import MathlibExt.CategoryTheory.Preadditive.SplitCokernel
public import MathlibExt.CategoryTheory.Preadditive.SplitKernel
public import MathlibExt.CategoryTheory.Preadditive.SplitFunctor

/-!
# The quotient by simplicial degeneracies

The cokernel of the Dold–Kan complementary projector
has the universal property of killing degeneracies.
It is identified with the normalized Moore complex.
The quotient projection is a chain homotopy equivalence,
and degree evaluation commutes with its cokernel.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology.NormalizedQuotient

variable {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C)

/-- The quotient of the alternating complex by its native degenerate projector. -/
def obj : ChainComplex C ℕ :=
  cokernel (DoldKan.QInfty (X := X))

/-- The original quotient projection, before any choice of normalization coordinates. -/
def projection : (alternatingFaceMapComplex C).obj X ⟶ obj X :=
  cokernel.π (DoldKan.QInfty (X := X))

/-- The complementary projector is killed by the quotient projection. -/
@[reassoc]
theorem Q_comp_projection : DoldKan.QInfty ≫ projection X = 0 :=
  cokernel.condition _

/-- The quotient retains the normalized projection unchanged. -/
@[reassoc]
theorem P_comp_projection : DoldKan.PInfty ≫ projection X = projection X := by
  have h := congrArg (fun f => f ≫ projection X)
    (DoldKan.PInfty_add_QInfty (X := X))
  simpa only [Preadditive.add_comp, Q_comp_projection, add_zero, Category.id_comp] using h

/-- The native cokernel projection is epic as a map of complexes. -/
instance projection_epi : Epi (projection X) := by
  dsimp only [projection]
  exact Cofork.IsColimit.epi
    (colimit.isColimit (parallelPair (DoldKan.QInfty (X := X)) 0))

/-- The native degenerate projector is the complement of its specified Moore splitting. -/
theorem Q_eq_splitComplement :
    DoldKan.QInfty (X := X) = 𝟙 _ -
      DoldKan.PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X := by
  apply eq_sub_iff_add_eq.mpr
  rw [DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  exact (add_comm _ _).trans (DoldKan.PInfty_add_QInfty (X := X))

section ProjectorPreservation

universe uD vD

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  (F : ChainComplex C ℕ ⥤ D) [F.Additive]

/-- Any additive functor preserves the kernel of the native degenerate projector. -/
theorem preservesKernel_Q :
    PreservesLimit (parallelPair (DoldKan.QInfty (X := X)) 0) F :=
  preservesKernel_splitComplement F (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- Any additive functor preserves the cokernel of the native degenerate projector. -/
theorem preservesCokernel_Q :
    PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0) F :=
  preservesCokernel_splitComplement F (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

end ProjectorPreservation

/-- Evaluation identifies the complex cokernel with the degree cokernel. -/
def evalIso (n : ℕ) :
    (obj X).X n ≅ cokernel ((DoldKan.QInfty (X := X)).f n) := by
  letI : PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0)
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n) :=
    preservesCokernel_Q X (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
  exact PreservesCokernel.iso (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    (DoldKan.QInfty (X := X))

/-- The degree comparison retains the original cokernel projection. -/
@[reassoc]
theorem projection_f_evalIso_hom (n : ℕ) :
    (projection X).f n ≫ (evalIso X n).hom =
      cokernel.π ((DoldKan.QInfty (X := X)).f n) :=
  PreservesCokernel.π_iso_hom (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    (DoldKan.QInfty (X := X))

/-- Each quotient component is epic, independently of its chosen cokernel object. -/
instance projection_f_epi (n : ℕ) : Epi ((projection X).f n) := by
  have hEpi : Epi ((projection X).f n ≫ (evalIso X n).hom) := by
    rw [projection_f_evalIso_hom]
    infer_instance
  exact (epi_comp_iff_of_isIso ((projection X).f n) (evalIso X n).hom).1 hEpi

/-- The complementary degree projector is killed by the quotient component. -/
@[reassoc]
theorem Q_f_comp_projection_f (n : ℕ) :
    (DoldKan.QInfty (X := X)).f n ≫ (projection X).f n = 0 :=
  congrArg (fun f => f.f n) (Q_comp_projection X)

/-- The simplicial degeneracy images vanish in the quotient. -/
@[reassoc]
theorem degeneracy_comp_projection (n : ℕ) (i : Fin (n + 1)) :
    X.σ i ≫ (projection X).f (n + 1) = 0 :=
  (DoldKan.degeneraciesVanish_iff_QInfty_f_comp ((projection X).f (n + 1))).2
    (Q_f_comp_projection_f X (n + 1)) |>.σ_comp i

/-- A degree map killing the degeneracies descends through the quotient. -/
def descAt (n : ℕ) {T : C} (f : X.obj (op ⦋n⦌) ⟶ T)
    (h : DoldKan.DegeneraciesVanish f) : (obj X).X n ⟶ T :=
  (evalIso X n).hom ≫ cokernel.desc ((DoldKan.QInfty (X := X)).f n) f
    ((DoldKan.degeneraciesVanish_iff_QInfty_f_comp f).1 h)

/-- The degreewise universal descent retains its original map. -/
@[reassoc]
theorem projection_f_descAt (n : ℕ) {T : C} (f : X.obj (op ⦋n⦌) ⟶ T)
    (h : DoldKan.DegeneraciesVanish f) :
    (projection X).f n ≫ descAt X n f h = f := by
  rw [descAt, ← Category.assoc, projection_f_evalIso_hom, cokernel.π_desc]

/-- The degreewise descent is uniquely characterized by its original projection square. -/
theorem descAt_unique (n : ℕ) {T : C} (f : X.obj (op ⦋n⦌) ⟶ T)
    (h : DoldKan.DegeneraciesVanish f) (g : (obj X).X n ⟶ T)
    (hg : (projection X).f n ≫ g = f) : g = descAt X n f h := by
  apply (cancel_epi ((projection X).f n)).1
  exact hg.trans (projection_f_descAt X n f h).symm

/-- An chain map killing all simplicial degeneracies has a canonical descent. -/
def desc {L : ChainComplex C ℕ} (f : (alternatingFaceMapComplex C).obj X ⟶ L)
    (h : ∀ n, DoldKan.DegeneraciesVanish (f.f n)) : obj X ⟶ L := by
  refine cokernel.desc (DoldKan.QInfty (X := X)) f ?_
  apply HomologicalComplex.hom_ext
  intro n
  change (DoldKan.QInfty (X := X)).f n ≫ f.f n = 0
  exact (DoldKan.degeneraciesVanish_iff_QInfty_f_comp (f.f n)).1 (h n)

/-- The universal chain map has exactly the original projection square. -/
@[reassoc]
theorem projection_desc {L : ChainComplex C ℕ}
    (f : (alternatingFaceMapComplex C).obj X ⟶ L)
    (h : ∀ n, DoldKan.DegeneraciesVanish (f.f n)) :
    projection X ≫ desc X f h = f :=
  cokernel.π_desc _ _ _

/-- The chain descent and degree descent are the same map. -/
theorem desc_f {L : ChainComplex C ℕ} (f : (alternatingFaceMapComplex C).obj X ⟶ L)
    (h : ∀ n, DoldKan.DegeneraciesVanish (f.f n)) (n : ℕ) :
    (desc X f h).f n = descAt X n (f.f n) (h n) := by
  apply (cancel_epi ((projection X).f n)).1
  exact (congrArg (fun g => g.f n) (projection_desc X f h)).trans
    (projection_f_descAt X n (f.f n) (h n)).symm

/-- The quotient is the native normalized Moore complex, by its universal property. -/
def mooreIso : obj X ≅ (normalizedMooreComplex C).obj X :=
  cokernelSplitComplementIso (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (by exact Q_eq_splitComplement X)

/-- The normalized comparison maps the original projection to the native normalized projection. -/
@[reassoc]
theorem projection_mooreIso_hom :
    projection X ≫ (mooreIso X).hom = DoldKan.PInftyToNormalizedMooreComplex X :=
  cokernelSplitComplementIso_π_hom (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (by exact Q_eq_splitComplement X)

/-- The inverse comparison is the native inclusion followed by the quotient projection. -/
theorem mooreIso_inv :
    (mooreIso X).inv = inclusionOfMooreComplexMap X ≫ projection X :=
  cokernelSplitComplementIso_inv (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (by exact Q_eq_splitComplement X)

/-- The quotient projection is a homotopy equivalence, from native normalization. -/
def projectionHomotopyEquiv :
    HomotopyEquiv ((alternatingFaceMapComplex C).obj X) (obj X) where
  hom := projection X
  inv := (mooreIso X).hom ≫ inclusionOfMooreComplexMap X
  homotopyHomInvId :=
    Homotopy.trans (Homotopy.ofEq (by
      rw [← Category.assoc, projection_mooreIso_hom]
      exact DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X))
      (DoldKan.homotopyPInftyToId X)
  homotopyInvHomId := Homotopy.ofEq (by
    rw [Category.assoc, ← mooreIso_inv]
    exact (mooreIso X).hom_inv_id)

/-- The homotopy equivalence uses the original quotient map as its forward map. -/
@[simp]
theorem projectionHomotopyEquiv_hom :
    (projectionHomotopyEquiv X).hom = projection X := rfl

/-- The quotient projection is a quasi-isomorphism for every simplicial object. -/
instance projection_quasiIso : QuasiIso (projection X) :=
  (projectionHomotopyEquiv X).quasiIso_hom

variable {X} {Y Z : SimplicialObject C}

/-- The original complex map commutes with the native degenerate projector. -/
@[reassoc]
theorem Q_naturality (f : X ⟶ Y) :
    DoldKan.QInfty (X := X) ≫ (alternatingFaceMapComplex C).map f =
      (alternatingFaceMapComplex C).map f ≫ DoldKan.QInfty (X := Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (DoldKan.QInfty_f_naturality n f).symm

/-- Native complementary-projector naturality induces the quotient map. -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  cokernel.map (DoldKan.QInfty (X := X)) (DoldKan.QInfty (X := Y))
    ((alternatingFaceMapComplex C).map f) ((alternatingFaceMapComplex C).map f)
    (Q_naturality f)

/-- The quotient map retains native alternating-map naturality. -/
@[reassoc]
theorem projection_map (f : X ⟶ Y) :
    projection X ≫ map f = (alternatingFaceMapComplex C).map f ≫ projection Y :=
  cokernel.π_desc _ _ _

/-- Quotienting retains identity maps. -/
@[simp]
theorem map_id (X : SimplicialObject C) : map (𝟙 X) = 𝟙 (obj X) := by
  apply (cancel_epi (projection X)).1
  rw [projection_map, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Quotienting retains the original composition order. -/
@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ≫ map g := by
  apply (cancel_epi (projection X)).1
  rw [projection_map, CategoryTheory.Functor.map_comp, Category.assoc,
    ← projection_map g, ← Category.assoc, ← projection_map f, Category.assoc]

variable (C)

/-- The normalization quotient functor, with its native maps. -/
def functor : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := obj
  map f := NormalizedQuotient.map f
  map_id X := NormalizedQuotient.map_id X
  map_comp f g := NormalizedQuotient.map_comp f g

/-- The projection, bundled naturally in the original simplicial object. -/
def projectionNatTrans : alternatingFaceMapComplex C ⟶ functor C where
  app X := projection X
  naturality _ _ f := (projection_map f).symm

/-- The quotient and native normalized Moore complex agree naturally. -/
def mooreNatIso : functor C ≅ normalizedMooreComplex C :=
  NatIso.ofComponents mooreIso (by
    intro X Y f
    exact cokernelSplitComplementIso_naturality (DoldKan.QInfty (X := X))
      (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
      (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
      (by exact Q_eq_splitComplement X)
      (DoldKan.QInfty (X := Y))
      (inclusionOfMooreComplexMap Y) (DoldKan.PInftyToNormalizedMooreComplex Y)
      (DoldKan.splitMonoInclusionOfMooreComplexMap Y).id
      (by exact Q_eq_splitComplement Y)
      ((alternatingFaceMapComplex C).map f) ((normalizedMooreComplex C).map f)
      (Q_naturality f)
      (DoldKan.PInftyToNormalizedMooreComplex_naturality f))

section KernelNormalization

variable {C} (X : SimplicialObject C)

/-- The kernel of the degenerate projector is the native normalized Moore complex. -/
def mooreKernelIso :
    kernel (DoldKan.QInfty (X := X)) ≅ (normalizedMooreComplex C).obj X :=
  kernelSplitComplementIso (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- The kernel comparison retains the original Moore inclusion. -/
@[reassoc]
theorem mooreKernelIso_hom_inclusion :
    (mooreKernelIso X).hom ≫ inclusionOfMooreComplexMap X =
      kernel.ι (DoldKan.QInfty (X := X)) :=
  kernelSplitComplementIso_hom_ι (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- The inverse is the native lift of the original Moore inclusion. -/
@[reassoc]
theorem mooreKernelIso_inv_ι :
    (mooreKernelIso X).inv ≫ kernel.ι (DoldKan.QInfty (X := X)) =
      inclusionOfMooreComplexMap X :=
  kernelSplitComplementIso_inv_ι (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- The forward comparison is the kernel inclusion followed by Moore projection. -/
theorem mooreKernelIso_hom :
    (mooreKernelIso X).hom =
      kernel.ι (DoldKan.QInfty (X := X)) ≫ DoldKan.PInftyToNormalizedMooreComplex X :=
  kernelSplitComplementIso_hom (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- The kernel and original quotient agree through the original ambient complex. -/
def kernelQuotientIso : kernel (DoldKan.QInfty (X := X)) ≅ obj X :=
  mooreKernelIso X ≪≫ (mooreIso X).symm

/-- The comparison is the kernel inclusion followed by the original quotient map. -/
theorem kernelQuotientIso_hom :
    (kernelQuotientIso X).hom =
      kernel.ι (DoldKan.QInfty (X := X)) ≫ projection X := by
  change (mooreKernelIso X).hom ≫ (mooreIso X).inv = _
  rw [mooreIso_inv, ← Category.assoc, mooreKernelIso_hom_inclusion]

/-- The restriction of the quotient to the kernel is an isomorphism. -/
instance kernel_ι_comp_projection_isIso :
    IsIso (kernel.ι (DoldKan.QInfty (X := X)) ≫ projection X) := by
  rw [← kernelQuotientIso_hom X]
  infer_instance

variable {X} {Y : SimplicialObject C}

/-- Original simplicial maps act naturally on the degeneracy kernel. -/
@[reassoc]
theorem mooreKernelIso_naturality (f : X ⟶ Y) :
    kernel.map (DoldKan.QInfty (X := X)) (DoldKan.QInfty (X := Y))
        ((alternatingFaceMapComplex C).map f) ((alternatingFaceMapComplex C).map f)
        (Q_naturality f) ≫ (mooreKernelIso Y).hom =
      (mooreKernelIso X).hom ≫ (normalizedMooreComplex C).map f :=
  kernelSplitComplementIso_naturality (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id (Q_eq_splitComplement X)
    (DoldKan.QInfty (X := Y))
    (inclusionOfMooreComplexMap Y) (DoldKan.PInftyToNormalizedMooreComplex Y)
    (DoldKan.splitMonoInclusionOfMooreComplexMap Y).id (Q_eq_splitComplement Y)
    ((alternatingFaceMapComplex C).map f) ((normalizedMooreComplex C).map f)
    (Q_naturality f) ((inclusionOfMooreComplex C).naturality f).symm

/-- The kernel-to-quotient comparison respects the original kernel and quotient maps. -/
@[reassoc]
theorem kernelQuotientIso_naturality (f : X ⟶ Y) :
    kernel.map (DoldKan.QInfty (X := X)) (DoldKan.QInfty (X := Y))
        ((alternatingFaceMapComplex C).map f) ((alternatingFaceMapComplex C).map f)
        (Q_naturality f) ≫ (kernelQuotientIso Y).hom =
      (kernelQuotientIso X).hom ≫ map f := by
  have hn : (normalizedMooreComplex C).map f ≫ (mooreIso Y).inv =
      (mooreIso X).inv ≫ map f :=
    (mooreNatIso C).inv.naturality f
  change _ ≫ ((mooreKernelIso Y).hom ≫ (mooreIso Y).inv) =
    ((mooreKernelIso X).hom ≫ (mooreIso X).inv) ≫ map f
  calc
    _ = (_ ≫ (mooreKernelIso Y).hom) ≫ (mooreIso Y).inv :=
      (Category.assoc _ _ _).symm
    _ = ((mooreKernelIso X).hom ≫ (normalizedMooreComplex C).map f) ≫
        (mooreIso Y).inv := by rw [mooreKernelIso_naturality]
    _ = (mooreKernelIso X).hom ≫
        ((normalizedMooreComplex C).map f ≫ (mooreIso Y).inv) := Category.assoc _ _ _
    _ = (mooreKernelIso X).hom ≫ ((mooreIso X).inv ≫ map f) := by rw [hn]
    _ = _ := (Category.assoc _ _ _).symm

end KernelNormalization

end AlgebraicTopology.NormalizedQuotient
