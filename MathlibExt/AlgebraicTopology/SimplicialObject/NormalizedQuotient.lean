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
# Normalization as a quotient by degenerate simplices

Let X be a simplicial object in an abelian category C. On its alternating-face chain complex
K_X, the Dold–Kan projectors P_X and Q_X are complementary, with P_X projecting onto the
normalized Moore subcomplex and Q_X onto degenerate chains. The cokernel L_X of Q_X has the
universal property of killing all simplicial degeneracies.

The quotient is isomorphic to the normalized Moore complex N_X. In degree n, N_X is the
intersection of the kernels of faces δ₁ through δ_n, and its differential is induced by δ₀.
Writing ι_X : N_X → K_X and ρ_X : K_X → N_X for the inclusion and retraction, Q_X = 𝟙 − ρ_X ≫
ι_X. The quotient projection is a chain homotopy equivalence, and the kernel of Q_X is also
naturally isomorphic to N_X and to L_X.

These comparisons preserve the projections and inclusions and are natural in simplicial maps.
Every additive functor from ChainComplex C ℕ to a preadditive category preserves the kernel
and cokernel of Q_X, so evaluation identifies each degree of L_X with the corresponding degree
cokernel. The object and morphism universes of both categories may be different.

See Weibel, *An Introduction to Homological Algebra*, Chapter 8, for normalization and the
Dold–Kan correspondence.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology.NormalizedQuotient

variable {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C)

/-- For a simplicial object X in an abelian category C, define L_X to be the cokernel in
ChainComplex C ℕ of the Dold–Kan degenerate projector Q_X on the alternating-face complex K_X.
Its quotient maps kill all simplicial degeneracy images. -/
def obj : ChainComplex C ℕ :=
  cokernel (DoldKan.QInfty (X := X))

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
The chain map projection X is π_X = cokernel.π Q_X. In each degree it maps a chain to its
class modulo the degenerate chains. -/
def projection : (alternatingFaceMapComplex C).obj X ⟶ obj X :=
  cokernel.π (DoldKan.QInfty (X := X))

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
One has Q_X ≫ π_X = 0 as a chain map K_X ⟶ L_X. -/
@[reassoc]
theorem Q_comp_projection : DoldKan.QInfty ≫ projection X = 0 :=
  cokernel.condition _

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For the complementary normalized projector P_X, one has P_X ≫ π_X = π_X. This follows from P_X
+ Q_X = 𝟙 K_X and Q_X ≫ π_X = 0. -/
@[reassoc]
theorem P_comp_projection : DoldKan.PInfty ≫ projection X = projection X := by
  have h := congrArg (fun f => f ≫ projection X)
    (DoldKan.PInfty_add_QInfty (X := X))
  simpa only [Preadditive.add_comp, Q_comp_projection, add_zero, Category.id_comp] using h

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
The cokernel projection π_X is an epimorphism in ChainComplex C ℕ. -/
instance projection_epi : Epi (projection X) := by
  dsimp only [projection]
  exact Cofork.IsColimit.epi
    (colimit.isColimit (parallelPair (DoldKan.QInfty (X := X)) 0))

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. Then Q_X = 𝟙 K_X − ρ_X ≫ ι_X, where ι_X ≫ ρ_X = 𝟙 N_X and ρ_X ≫ ι_X = P_X. -/
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

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let D be a preadditive category and F : ChainComplex C ℕ ⥤ D an additive functor. Then F
preserves the limit of the parallel pair Q_X and 0, that is, the kernel of this particular
projector. The conclusion follows from its split-complement presentation. -/
theorem preservesKernel_Q :
    PreservesLimit (parallelPair (DoldKan.QInfty (X := X)) 0) F :=
  preservesKernel_splitComplement F (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let D be a preadditive category and F : ChainComplex C ℕ ⥤ D an additive functor. Then F
preserves the colimit of the parallel pair Q_X and 0, that is, the cokernel of this particular
projector, by its split-complement presentation. -/
theorem preservesCokernel_Q :
    PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0) F :=
  preservesCokernel_splitComplement F (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

end ProjectorPreservation

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For every n : ℕ, evaluation at n gives an isomorphism e_(X,n) : (L_X)_n ≅ cokernel (Q_X.f n)
in C. It is the cokernel-preservation comparison for the degree-evaluation functor. -/
def evalIso (n : ℕ) :
    (obj X).X n ≅ cokernel ((DoldKan.QInfty (X := X)).f n) := by
  letI : PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0)
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n) :=
    preservesCokernel_Q X (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
  exact PreservesCokernel.iso (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    (DoldKan.QInfty (X := X))

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For n : ℕ, let e_(X,n) : (L_X)_n ≅ cokernel (Q_X.f n) be evalIso X n. Then π_X.f n ≫
e_(X,n).hom = cokernel.π (Q_X.f n). -/
@[reassoc]
theorem projection_f_evalIso_hom (n : ℕ) :
    (projection X).f n ≫ (evalIso X n).hom =
      cokernel.π ((DoldKan.QInfty (X := X)).f n) :=
  PreservesCokernel.π_iso_hom (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    (DoldKan.QInfty (X := X))

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For each n : ℕ, the component π_X.f n : X_n ⟶ (L_X)_n is an epimorphism in C. Its composition
with evalIso X n is the degree cokernel projection. -/
instance projection_f_epi (n : ℕ) : Epi ((projection X).f n) := by
  have hEpi : Epi ((projection X).f n ≫ (evalIso X n).hom) := by
    rw [projection_f_evalIso_hom]
    infer_instance
  exact (epi_comp_iff_of_isIso ((projection X).f n) (evalIso X n).hom).1 hEpi

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For every n : ℕ, Q_X.f n ≫ π_X.f n = 0 as a morphism X_n ⟶ (L_X)_n. -/
@[reassoc]
theorem Q_f_comp_projection_f (n : ℕ) :
    (DoldKan.QInfty (X := X)).f n ≫ (projection X).f n = 0 :=
  congrArg (fun f => f.f n) (Q_comp_projection X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For every n : ℕ and i : Fin (n + 1), X.σ i ≫ π_X.f (n + 1) = 0. Thus the quotient map in
degree n + 1 kills the image of each degeneracy X_n ⟶ X_(n+1). -/
@[reassoc]
theorem degeneracy_comp_projection (n : ℕ) (i : Fin (n + 1)) :
    X.σ i ≫ (projection X).f (n + 1) = 0 :=
  (DoldKan.degeneraciesVanish_iff_QInfty_f_comp ((projection X).f (n + 1))).2
    (Q_f_comp_projection_f X (n + 1)) |>.σ_comp i

/-- For a simplicial object X in an abelian category C, let L_X be the cokernel of its degenerate
projector on the alternating-face complex, and let π_(X,n) : X_n ⟶ (L_X)_n be the degree-n
quotient map. For T : C and a map f : X_n ⟶ T satisfying DoldKan.DegeneraciesVanish f, define
descAt X n f h : (L_X)_n ⟶ T by transport to the degree cokernel and its universal descent.
The degeneracy-vanishing condition is automatic in degree 0; in degree n = k + 1 it means σ_i
≫ f = 0 for all i : Fin (k + 1). The defining equation is π_(X,n) ≫ descAt X n f h = f. -/
def descAt (n : ℕ) {T : C} (f : X.obj (op ⦋n⦌) ⟶ T)
    (h : DoldKan.DegeneraciesVanish f) : (obj X).X n ⟶ T :=
  (evalIso X n).hom ≫ cokernel.desc ((DoldKan.QInfty (X := X)).f n) f
    ((DoldKan.degeneraciesVanish_iff_QInfty_f_comp f).1 h)

/-- For a simplicial object X in an abelian category C, let L_X be the cokernel of its degenerate
projector on the alternating-face complex, and let π_(X,n) : X_n ⟶ (L_X)_n be the degree-n
quotient map. If f : X_n ⟶ T kills every degeneracy into degree n, then π_(X,n) ≫ descAt X n f
h = f. The degeneracy-vanishing condition is automatic in degree 0; in degree n = k + 1 it
means σ_i ≫ f = 0 for all i : Fin (k + 1). -/
@[reassoc]
theorem projection_f_descAt (n : ℕ) {T : C} (f : X.obj (op ⦋n⦌) ⟶ T)
    (h : DoldKan.DegeneraciesVanish f) :
    (projection X).f n ≫ descAt X n f h = f := by
  rw [descAt, ← Category.assoc, projection_f_evalIso_hom, cokernel.π_desc]

/-- For a simplicial object X in an abelian category C, let L_X be the cokernel of its degenerate
projector on the alternating-face complex, and let π_(X,n) : X_n ⟶ (L_X)_n be the degree-n
quotient map. Let f : X_n ⟶ T kill every degeneracy into degree n, and let g : (L_X)_n ⟶ T
satisfy π_(X,n) ≫ g = f. Then g = descAt X n f h. The degeneracy-vanishing condition is
automatic in degree 0; in degree n = k + 1 it means σ_i ≫ f = 0 for all i : Fin (k + 1). -/
theorem descAt_unique (n : ℕ) {T : C} (f : X.obj (op ⦋n⦌) ⟶ T)
    (h : DoldKan.DegeneraciesVanish f) (g : (obj X).X n ⟶ T)
    (hg : (projection X).f n ≫ g = f) : g = descAt X n f h := by
  apply (cancel_epi ((projection X).f n)).1
  exact hg.trans (projection_f_descAt X n f h).symm

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let L be another chain complex and f : K_X ⟶ L a chain map. Assume σ_i ≫ f_(k+1) = 0 for every
k : ℕ and i : Fin (k + 1). Then desc X f h : L_X ⟶ L is the unique cokernel descent of f,
characterized by π_X ≫ desc X f h = f. -/
def desc {L : ChainComplex C ℕ} (f : (alternatingFaceMapComplex C).obj X ⟶ L)
    (h : ∀ n, DoldKan.DegeneraciesVanish (f.f n)) : obj X ⟶ L := by
  refine cokernel.desc (DoldKan.QInfty (X := X)) f ?_
  apply HomologicalComplex.hom_ext
  intro n
  change (DoldKan.QInfty (X := X)).f n ≫ f.f n = 0
  exact (DoldKan.degeneraciesVanish_iff_QInfty_f_comp (f.f n)).1 (h n)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For a chain map f : K_X ⟶ L killing all degeneracies in every degree, one has π_X ≫ desc X f h
= f. Explicitly, the hypothesis is σ_i ≫ f_(k+1) = 0 for every k : ℕ and i : Fin (k + 1). -/
@[reassoc]
theorem projection_desc {L : ChainComplex C ℕ}
    (f : (alternatingFaceMapComplex C).obj X ⟶ L)
    (h : ∀ n, DoldKan.DegeneraciesVanish (f.f n)) :
    projection X ≫ desc X f h = f :=
  cokernel.π_desc _ _ _

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let f : K_X ⟶ L kill every simplicial degeneracy in every degree. For each n : ℕ, the degree
component of desc X f h equals descAt X n (f.f n) (h n), where both maps are characterized by
precomposition with π_X.f n. -/
theorem desc_f {L : ChainComplex C ℕ} (f : (alternatingFaceMapComplex C).obj X ⟶ L)
    (h : ∀ n, DoldKan.DegeneraciesVanish (f.f n)) (n : ℕ) :
    (desc X f h).f n = descAt X n (f.f n) (h n) := by
  apply (cancel_epi ((projection X).f n)).1
  exact (congrArg (fun g => g.f n) (projection_desc X f h)).trans
    (projection_f_descAt X n (f.f n) (h n)).symm

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. The isomorphism e_X : L_X ≅ N_X is characterized by π_X ≫ e_X.hom = ρ_X; its
inverse is ι_X ≫ π_X. The normalized degree-n object is the intersection of the kernels of δ₁
through δ_n, with differential induced by δ₀. -/
def mooreIso : obj X ≅ (normalizedMooreComplex C).obj X :=
  cokernelSplitComplementIso (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (by exact Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. For e_X = mooreIso X : L_X ≅ N_X, one has π_X ≫ e_X.hom = ρ_X, where ρ_X is
DoldKan.PInftyToNormalizedMooreComplex X. -/
@[reassoc]
theorem projection_mooreIso_hom :
    projection X ≫ (mooreIso X).hom = DoldKan.PInftyToNormalizedMooreComplex X :=
  cokernelSplitComplementIso_π_hom (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (by exact Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. The inverse of mooreIso X : L_X ≅ N_X is ι_X ≫ π_X, a chain map N_X ⟶ L_X. -/
theorem mooreIso_inv :
    (mooreIso X).inv = inclusionOfMooreComplexMap X ≫ projection X :=
  cokernelSplitComplementIso_inv (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (by exact Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. There is a chain homotopy equivalence K_X ≃ L_X whose forward map is π_X and
inverse is (mooreIso X).hom ≫ ι_X. Their composite on K_X is P_X, homotopic to 𝟙 K_X; their
composite on L_X is exactly 𝟙 L_X. -/
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

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
The forward map of projectionHomotopyEquiv X : HomotopyEquiv K_X L_X is π_X, the cokernel
projection of Q_X. -/
@[simp]
theorem projectionHomotopyEquiv_hom :
    (projectionHomotopyEquiv X).hom = projection X := rfl

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
The chain map π_X is a quasi-isomorphism: its induced map H_n(K_X) ⟶ H_n(L_X) is an
isomorphism for every n : ℕ, because π_X is a chain homotopy equivalence. -/
instance projection_quasiIso : QuasiIso (projection X) :=
  (projectionHomotopyEquiv X).quasiIso_hom

variable {X} {Y Z : SimplicialObject C}

/-- In an abelian category C, let f : X ⟶ Y be a simplicial map and K(f) : K_X ⟶ K_Y its
alternating-face chain map. Let Q_X and Q_Y be the degenerate projectors and L_X and L_Y their
cokernels. The projectors satisfy Q_X ≫ K(f) = K(f) ≫ Q_Y as chain maps K_X ⟶ K_Y. -/
@[reassoc]
theorem Q_naturality (f : X ⟶ Y) :
    DoldKan.QInfty (X := X) ≫ (alternatingFaceMapComplex C).map f =
      (alternatingFaceMapComplex C).map f ≫ DoldKan.QInfty (X := Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (DoldKan.QInfty_f_naturality n f).symm

/-- In an abelian category C, let f : X ⟶ Y be a simplicial map and K(f) : K_X ⟶ K_Y its
alternating-face chain map. Let Q_X and Q_Y be the degenerate projectors and L_X and L_Y their
cokernels. The commutation Q_X ≫ K(f) = K(f) ≫ Q_Y induces map f : L_X ⟶ L_Y by the cokernel
map. It is characterized by π_X ≫ map f = K(f) ≫ π_Y, where π_X and π_Y are the quotient
projections. -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  cokernel.map (DoldKan.QInfty (X := X)) (DoldKan.QInfty (X := Y))
    ((alternatingFaceMapComplex C).map f) ((alternatingFaceMapComplex C).map f)
    (Q_naturality f)

/-- In an abelian category C, let f : X ⟶ Y be a simplicial map and K(f) : K_X ⟶ K_Y its
alternating-face chain map. Let Q_X and Q_Y be the degenerate projectors and L_X and L_Y their
cokernels. The induced quotient map map f satisfies π_X ≫ map f = K(f) ≫ π_Y, where π_X : K_X
⟶ L_X and π_Y : K_Y ⟶ L_Y are the cokernel projections. -/
@[reassoc]
theorem projection_map (f : X ⟶ Y) :
    projection X ≫ map f = (alternatingFaceMapComplex C).map f ≫ projection Y :=
  cokernel.π_desc _ _ _

/-- For a simplicial object X in an abelian category C, let L_X be the cokernel of the degenerate
projector on its alternating-face complex. The map induced on this quotient by the simplicial
identity satisfies map (𝟙 X) = 𝟙 L_X. -/
@[simp]
theorem map_id (X : SimplicialObject C) : map (𝟙 X) = 𝟙 (obj X) := by
  apply (cancel_epi (projection X)).1
  rw [projection_map, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- For simplicial maps f : X ⟶ Y and g : Y ⟶ Z in an abelian category C, the induced maps on the
degenerate-projector cokernels satisfy map (f ≫ g) = map f ≫ map g. The source and target
quotients are those of the alternating-face complexes. -/
@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ≫ map g := by
  apply (cancel_epi (projection X)).1
  rw [projection_map, CategoryTheory.Functor.map_comp, Category.assoc,
    ← projection_map g, ← Category.assoc, ← projection_map f, Category.assoc]

variable (C)

/-- For an abelian category C, the functor SimplicialObject C ⥤ ChainComplex C ℕ sends X to the
cokernel of its Dold–Kan degenerate projector Q_X on the alternating-face complex. It sends a
simplicial map to the corresponding cokernel map induced by its alternating-face chain map. -/
def functor : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := obj
  map f := NormalizedQuotient.map f
  map_id X := NormalizedQuotient.map_id X
  map_comp f g := NormalizedQuotient.map_comp f g

/-- For an abelian category C, the chain maps π_X from the alternating-face complexes K_X to the
degenerate-chain quotients L_X form a natural transformation alternatingFaceMapComplex C ⟶
NormalizedQuotient.functor C. Naturality for f : X ⟶ Y is K(f) ≫ π_Y = π_X ≫ map f. -/
def projectionNatTrans : alternatingFaceMapComplex C ⟶ functor C where
  app X := projection X
  naturality _ _ f := (projection_map f).symm

/-- For an abelian category C, the maps e_X = mooreIso X : L_X ≅ N_X form a natural isomorphism
from the degenerate-chain quotient functor to normalizedMooreComplex C. Here π_X ≫ e_X.hom is
the Moore retraction and e_X.inv is Moore inclusion followed by π_X. For f : X ⟶ Y, map f ≫
e_Y.hom = e_X.hom ≫ N(f). -/
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

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. There is an isomorphism a_X : kernel Q_X ≅ N_X. If κ_X : kernel Q_X ⟶ K_X is the
kernel inclusion, then a_X.hom = κ_X ≫ ρ_X and a_X.hom ≫ ι_X = κ_X. -/
def mooreKernelIso :
    kernel (DoldKan.QInfty (X := X)) ≅ (normalizedMooreComplex C).obj X :=
  kernelSplitComplementIso (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. Writing κ_X for the kernel inclusion of Q_X and a_X = mooreKernelIso X : kernel Q_X
≅ N_X, one has a_X.hom ≫ ι_X = κ_X. -/
@[reassoc]
theorem mooreKernelIso_hom_inclusion :
    (mooreKernelIso X).hom ≫ inclusionOfMooreComplexMap X =
      kernel.ι (DoldKan.QInfty (X := X)) :=
  kernelSplitComplementIso_hom_ι (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. For a_X = mooreKernelIso X : kernel Q_X ≅ N_X and κ_X : kernel Q_X ⟶ K_X, the
inverse satisfies a_X.inv ≫ κ_X = ι_X. Thus it is the kernel lift of the Moore inclusion. -/
@[reassoc]
theorem mooreKernelIso_inv_ι :
    (mooreKernelIso X).inv ≫ kernel.ι (DoldKan.QInfty (X := X)) =
      inclusionOfMooreComplexMap X :=
  kernelSplitComplementIso_inv_ι (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
Let N_X be the normalized Moore complex, with inclusion ι_X : N_X ⟶ K_X and retraction ρ_X :
K_X ⟶ N_X. The forward map of mooreKernelIso X is κ_X ≫ ρ_X, where κ_X : kernel Q_X ⟶ K_X is
the kernel inclusion. -/
theorem mooreKernelIso_hom :
    (mooreKernelIso X).hom =
      kernel.ι (DoldKan.QInfty (X := X)) ≫ DoldKan.PInftyToNormalizedMooreComplex X :=
  kernelSplitComplementIso_hom (DoldKan.QInfty (X := X))
    (inclusionOfMooreComplexMap X) (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
    (Q_eq_splitComplement X)

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
The kernel-to-Moore comparison followed by the inverse quotient-to-Moore comparison gives
kernelQuotientIso X : kernel Q_X ≅ L_X. Its forward map is κ_X ≫ π_X, where κ_X is the kernel
inclusion. -/
def kernelQuotientIso : kernel (DoldKan.QInfty (X := X)) ≅ obj X :=
  mooreKernelIso X ≪≫ (mooreIso X).symm

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
For κ_X : kernel Q_X ⟶ K_X, the forward map of kernelQuotientIso X : kernel Q_X ≅ L_X is
exactly κ_X ≫ π_X. -/
theorem kernelQuotientIso_hom :
    (kernelQuotientIso X).hom =
      kernel.ι (DoldKan.QInfty (X := X)) ≫ projection X := by
  change (mooreKernelIso X).hom ≫ (mooreIso X).inv = _
  rw [mooreIso_inv, ← Category.assoc, mooreKernelIso_hom_inclusion]

/-- For a simplicial object X in an abelian category C, let K_X be its alternating-face complex,
Q_X its Dold–Kan degenerate projector, L_X = cokernel Q_X and π_X : K_X ⟶ L_X the projection.
The morphism κ_X ≫ π_X : kernel Q_X ⟶ L_X is an isomorphism, where κ_X is the kernel
inclusion. It is the forward map of kernelQuotientIso X. -/
instance kernel_ι_comp_projection_isIso :
    IsIso (kernel.ι (DoldKan.QInfty (X := X)) ≫ projection X) := by
  rw [← kernelQuotientIso_hom X]
  infer_instance

variable {X} {Y : SimplicialObject C}

/-- In an abelian category C, let f : X ⟶ Y be a simplicial map and K(f) : K_X ⟶ K_Y its
alternating-face chain map. Let Q_X and Q_Y be the degenerate projectors and L_X and L_Y their
cokernels. Let a_X : kernel Q_X ≅ N_X and a_Y : kernel Q_Y ≅ N_Y be the Moore-kernel
comparisons. The kernel map k(f) induced by K(f) and the projector commutation satisfies k(f)
≫ a_Y.hom = a_X.hom ≫ N(f), where N(f) is the normalized Moore chain map. -/
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

/-- In an abelian category C, let f : X ⟶ Y be a simplicial map and K(f) : K_X ⟶ K_Y its
alternating-face chain map. Let Q_X and Q_Y be the degenerate projectors and L_X and L_Y their
cokernels. Let b_X : kernel Q_X ≅ L_X and b_Y : kernel Q_Y ≅ L_Y be kernelQuotientIso. The
kernel map k(f) induced by the commuting projectors and K(f) satisfies k(f) ≫ b_Y.hom =
b_X.hom ≫ map f, where map f is the induced quotient chain map. -/
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
