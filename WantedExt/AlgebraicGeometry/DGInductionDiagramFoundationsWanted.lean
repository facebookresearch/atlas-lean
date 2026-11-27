/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGInductionSplittingModels
public import MathlibExt.CategoryTheory.DGModuleBarDiagramModels
public import MathlibExt.CategoryTheory.DGModuleUniversalConeModels
public import MathlibExt.CategoryTheory.DGCoherentIndexModels

/-!
# Wanted actual induction coherence and whole-diagram bar constructions

All objects, units, bar paths, representable maps and higher category
cells have fixed native formulas. These are shared construction requests;
none returns a glued CY nondegeneracy assertion.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, §§2/4/6;
Keller, Deriving DG categories, §6; Bousfield--Kan, XII.
-/

namespace WantedExt.AlgebraicGeometry.DGInductionDiagramFoundationsWanted

open CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGBimodulePushforwardModels
open MathlibExt.CategoryTheory.DGInductionCoherenceModels
open MathlibExt.CategoryTheory.DGModuleBiproductModels
open MathlibExt.CategoryTheory.DGInductionSplittingModels
open MathlibExt.CategoryTheory.DGMoritaCospanModels
open MathlibExt.CategoryTheory.DGModuleBarDiagramModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGCoherentIndexModels

universe u

/-- Identity restriction is normalized on the actual module values. -/
def_wanted dg_restriction_identity (k : Type u) [Field k] (A : DGCat k)
    (T : EnvelopingMap (𝟙 A)) (R : RestrictionModel T.functor) : RestrictionIdentityModel A T R

/-- The actual induction identity is its fixed enriched-adjunction mate. -/
def_wanted dg_induction_identity (k : Type u) [Field k] (A : DGCat k)
    (T : EnvelopingMap (𝟙 A)) (R : RestrictionModel T.functor) (L : ExtensionModel T.functor R)
    (I : RestrictionIdentityModel A T R) : InductionIdentityModel L I

/-- Restriction composition keeps the same actual transported object and module action. -/
def_wanted dg_restriction_composition (k : Type u) [Field k] (A B C : DGCat k)
    (f : A ⟶ B) (g : B ⟶ C) (Tf : EnvelopingMap f) (Tg : EnvelopingMap g)
    (Tfg : EnvelopingMap (f ≫ g)) (Rf : RestrictionModel Tf.functor)
    (Rg : RestrictionModel Tg.functor) (Rfg : RestrictionModel Tfg.functor) :
  RestrictionCompositionModel f g Tf Tg Tfg Rf Rg Rfg

/-- Induction composition is the native adjunction transpose of the actual composite units. -/
def_wanted dg_induction_composition (k : Type u) [Field k] (A B C : DGCat k)
    (f : A ⟶ B) (g : B ⟶ C) (Tf : EnvelopingMap f) (Tg : EnvelopingMap g)
    (Tfg : EnvelopingMap (f ≫ g)) (Rf : RestrictionModel Tf.functor)
    (Rg : RestrictionModel Tg.functor) (Rfg : RestrictionModel Tfg.functor)
    (Lf : ExtensionModel Tf.functor Rf) (Lg : ExtensionModel Tg.functor Rg)
    (Lfg : ExtensionModel Tfg.functor Rfg)
    (R : RestrictionCompositionModel f g Tf Tg Tfg Rf Rg Rfg) : InductionCompositionModel Lf Lg Lfg R

/-- Projective module biproducts have all four native structural maps and block actions fixed. -/
def_wanted dg_module_biproduct (k : Type u) [Field k] (C : DGCat k)
    (M N : DGDerivedModules k C) : CofibrantBiproductModel M N

/-- The map of actual biproducts is normalized by both source inclusions. -/
def_wanted dg_module_biproduct_map (k : Type u) [Field k] (C : DGCat k)
    (M N M' N' : RightModule k C) (P : ModuleBiproductModel M N)
    (Q : ModuleBiproductModel M' N') (f : M ⟶ M') (g : N ⟶ N') : ModuleBiproductMapModel P Q f g

/-- The actual left dual map is representable Hom precomposition. -/
def_wanted dg_module_dual_map (k : Type u) [Field k] (C : DGCat k)
    (M N : DGDerivedModules k (enveloping C C)) (f : M.obj ⟶ N.obj)
    (DM : ModuleLeftDualModel C M) (DN : ModuleLeftDualModel C N) : ModuleDualMapModel M N f DM DN

/-- Left duality splits actual finite module biproducts through the same source inclusions. -/
def_wanted dg_module_dual_biproduct (k : Type u) [Field k] (C : DGCat k)
    (M N : DGDerivedModules k (enveloping C C)) (P : CofibrantBiproductModel M N)
    (DM : ModuleLeftDualModel C M) (DN : ModuleLeftDualModel C N)
    (DP : ModuleLeftDualModel C (⟨P.module, P.cofibrant⟩)) : ModuleDualBiproductModel M N P DM DN DP

/-- The full projective diagram bar fixes all coefficients, faces, augmentation and edge/higher cells. -/
def_wanted dg_module_bar_diagram_replacement (k : Type u) [Field k]
    (C : DGCat k) (J : Type u) [Category.{u} J] (D : J ⥤ RightModule k C)
    (pointwise : ∀ j : J, IsCofibrantModule (D.obj j)) : BarProjectiveDiagramReplacement D

/-- The pushed diagonal of a genuine DG coproduct splits by its fixed bar-inclusion unit mates. -/
def_wanted dg_pushed_diagonal_split (k : Type u) [Field k] (A B X : DGCat k)
    (P : DGCoproductModel A B) (f : P.category ⟶ X)
    (Ta : EnvelopingMap P.inl) (Tb : EnvelopingMap P.inr) (Tf : EnvelopingMap f)
    (Tea : EnvelopingMap (P.inl ≫ f)) (Teb : EnvelopingMap (P.inr ≫ f))
    (Ra : RestrictionModel Ta.functor) (Rb : RestrictionModel Tb.functor)
    (Rf : RestrictionModel Tf.functor) (Rea : RestrictionModel Tea.functor) (Reb : RestrictionModel Teb.functor)
    (Lf : ExtensionModel Tf.functor Rf) (Lea : ExtensionModel Tea.functor Rea) (Leb : ExtensionModel Teb.functor Reb)
    (CA : RestrictionCompositionModel P.inl f Ta Tf Tea Ra Rf Rea)
    (CB : RestrictionCompositionModel P.inr f Tb Tf Teb Rb Rf Reb)
    (DA : EnvelopingModuleModel (diagonal A)) (DB : EnvelopingModuleModel (diagonal B))
    (DD : EnvelopingModuleModel (diagonal P.category))
    (FA : FreeDiagonalSystem A) (FB : FreeDiagonalSystem B) (FD : FreeDiagonalSystem P.category)
    (PA : BarDiagonalModel DA FA) (PB : BarDiagonalModel DB FB) (PD : BarDiagonalModel DD FD)
    (ba : BarRestrictionMapModel P.inl Ta Ra PA PD) (bb : BarRestrictionMapModel P.inr Tb Rb PB PD) :
  PushedDiagonalSplitModel P f Ta Tb Tf Tea Teb Ra Rb Rf Rea Reb Lf Lea Leb CA CB PA PB PD ba bb

/-- The actual shifted module morphism is normalized at every point. -/
def_wanted dg_diagram_module_shift_map (k : Type u) [Field k] (C : DGCat k)
    (M N : RightModule k C) (f : M ⟶ N) (n : ℤ)
    (SM : ModuleShiftModel M n) (SN : ModuleShiftModel N n) : ModuleShiftMapModel f n SM SN

/-- Shifting the source adjunction unit fixes the entire induction comparison. -/
def_wanted dg_diagram_shifted_induction_unit (k : Type u) [Field k] (A B : DGCat k)
    (f : A ⟶ B) (T : EnvelopingMap f) (R : RestrictionModel T.functor)
    (L : ExtensionModel T.functor R) (M : DGDerivedModules k (enveloping A A)) (n : ℤ)
    (SM : CofibrantShiftModel M n) (SN : CofibrantShiftModel (L.functor.obj M) n) :
  ShiftedInductionUnitModel L M n SM SN

/-- Induction/shift commutation is the actual native enriched adjunction mate. -/
def_wanted dg_diagram_induction_shift (k : Type u) [Field k] (A B : DGCat k)
    (f : A ⟶ B) (T : EnvelopingMap f) (R : RestrictionModel T.functor)
    (L : ExtensionModel T.functor R) (M : DGDerivedModules k (enveloping A A)) (n : ℤ)
    (SM : CofibrantShiftModel M n) (SN : CofibrantShiftModel (L.functor.obj M) n)
    (U : ShiftedInductionUnitModel L M n SM SN) : InductionShiftModel L M n SM SN U

/-- Native descent from a module biproduct is fixed on both blocks. -/
def_wanted dg_diagram_biproduct_desc (k : Type u) [Field k] (C : DGCat k)
    (M N V : RightModule k C) (Q : ModuleBiproductModel M N) (a : M ⟶ V) (b : N ⟶ V) :
  ModuleBiproductDescModel Q a b

/-- Native lift to a module biproduct is fixed on both projections. -/
def_wanted dg_diagram_biproduct_lift (k : Type u) [Field k] (C : DGCat k)
    (M N V : RightModule k C) (Q : ModuleBiproductModel M N) (a : V ⟶ M) (b : V ⟶ N) :
  ModuleBiproductLiftModel Q a b

/-- The native cone descent has its full degree -1 homotopy block fixed. -/
def_wanted dg_diagram_cone_desc (k : Type u) [Field k] (C : DGCat k)
    (M N V : RightModule k C) (f : M ⟶ N) (Q : ModuleConeModel f) (b : N ⟶ V)
    (h : DGHom k (-1) M V) (boundary : dgDifferential k (-1) h = moduleCycle (f ≫ b)) :
  ModuleConeDescModel f Q b h boundary

/-- For closed maps $f : M \to N$ and $g : M' \to N'$ of right DG modules over a DG category $C$
over a field $k$, with cone models $Q$ of $f$ and $Q'$ of $g$, closed maps $a : M \to M'$ and
$b : N \to N'$, and a degree $-1$ map $h : M \to N'$ with $dh = b \circ f - g \circ a$: a map from
the cone of $f$ to the cone of $g$ which, at every object of $C$ and under the identifications of
$Q$ and $Q'$ with the mapping cones of the components of $f$ and $g$ (in degree $r$, the terms
$M^{r+1} \oplus N^r$ and $(M')^{r+1} \oplus (N')^r$, with the conventions of
`CochainComplex.mappingCone`), has the blocks $a : M^{r+1} \to (M')^{r+1}$,
$h : M^{r+1} \to (N')^r$ and $b : N^r \to (N')^r$. -/
def_wanted dg_diagram_cone_map (k : Type u) [Field k] (C : DGCat k)
    (M N M' N' : RightModule k C) (f : M ⟶ N) (g : M' ⟶ N')
    (Q : ModuleConeModel f) (Q' : ModuleConeModel g) (a : M ⟶ M') (b : N ⟶ N')
    (h : DGHom k (-1) M N')
    (boundary : dgDifferential k (-1) h = moduleCycle (f ≫ b) - moduleCycle (a ≫ g)) :
  ModuleConeMapModel f g Q Q' a b h boundary

/-- Construct the actual free DG bar/cobar index, with every word and every chain differential fixed. -/
def_wanted dg_coherent_poset_index (k : Type u) [Field k] (J : Type u) [PartialOrder J] :
  CoherentIndexModel k J

end WantedExt.AlgebraicGeometry.DGInductionDiagramFoundationsWanted
