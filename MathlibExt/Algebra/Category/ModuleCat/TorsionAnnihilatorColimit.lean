/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.DirectedSubmoduleColimit
public import MathlibExt.Algebra.Category.ModuleCat.TorsionFunctor

/-!
# Power torsion as the directed union of power annihilators

Let `R` be a commutative ring, `I` an ideal, and `M` an `R`-module in an independent carrier
universe. The submodule `Ann_M(I^n)` consists of elements killed by every scalar in `I^n`.
These submodules increase with `n`, and their union is `Γ_I(M) = Ideal.primaryComponent M I`.

Their inclusion maps define a natural-number diagram whose canonical cocone in `Γ_I(M)` is a
colimit. A module map preserves each power annihilator and induces both the diagram
transformation and the power-torsion map. These maps commute with the index inclusions.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.Torsion

variable {R : Type u} [CommRing R]

/-- Submodule annihilated by an ideal power.

For natural `n`, `powerAnnihilator I M n` is the submodule of elements `x : M` satisfying `r •
x = 0` for every `r ∈ I^n`. -/
def powerAnnihilator (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M (I ^ n : Ideal R)

/-- Power-annihilator submodules increase with the exponent.

If `i ≤ j`, then `Ann_M(I^i) ≤ Ann_M(I^j)`, because `I^j ≤ I^i`. -/
lemma powerAnnihilator_monotone (I : Ideal R) (M : ModuleCat.{v} R) :
    Monotone (powerAnnihilator I M) :=
  fun i j hij => Submodule.torsionBySet_le_torsionBySet_pow i j hij I

/-- Natural-number diagram of power-annihilator inclusions.

The diagram has degree-`n` object `ModuleCat.of R (powerAnnihilator I M n)` and, for `i ≤ j`,
the inclusion of the corresponding annihilator submodules. -/
def annihilatorDiagram (I : Ideal R) (M : ModuleCat.{v} R) : ℕ ⥤ ModuleCat.{v} R :=
  DirectedSubmoduleColimit.diagram (powerAnnihilator I M) (powerAnnihilator_monotone I M)

/-- Power-annihilator cocone in the power-torsion module.

The directed power-annihilator diagram has a canonical cocone whose point is their supremum,
the power-torsion module `Γ_I(M)`. -/
def annihilatorCocone (I : Ideal R) (M : ModuleCat.{v} R) : Cocone (annihilatorDiagram I M) :=
  DirectedSubmoduleColimit.cocone (powerAnnihilator I M) (powerAnnihilator_monotone I M)

/-- Power-annihilator cocone point is the primary component.

The point of `annihilatorCocone I M` equals `(ModuleCat.Torsion.functor I).obj M`, the module
`Γ_I(M)`. -/
lemma annihilatorCocone_point (I : Ideal R) (M : ModuleCat.{v} R) :
    (annihilatorCocone I M).pt = (functor I).obj M := rfl

/-- Inclusion of one power annihilator into power torsion.

The degree-`n` cocone map includes the submodule `Ann_M(I^n)` into `Γ_I(M)`. -/
def annihilatorInclusion (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    ModuleCat.of R (powerAnnihilator I M n) ⟶ (functor I).obj M :=
  (annihilatorCocone I M).ι.app n

/-- Power-annihilator inclusion preserves the underlying element.

For `x : Ann_M(I^n)`, the underlying element of its image in `Γ_I(M)` is `x.val`. -/
lemma annihilatorInclusion_val (I : Ideal R) (M : ModuleCat.{v} R)
    (n : ℕ) (x : powerAnnihilator I M n) :
    ((annihilatorInclusion I M n).hom x).val = x.val := rfl

/-- Directed power-annihilator cocone is a colimit.

The canonical cocone from the increasing power-annihilator submodules to `Γ_I(M)` satisfies
the colimit universal property in the same module category. -/
def annihilatorIsColimit (I : Ideal R) (M : ModuleCat.{v} R) :
    IsColimit (annihilatorCocone I M) :=
  DirectedSubmoduleColimit.isColimit (powerAnnihilator I M) (powerAnnihilator_monotone I M)

/-- Power-annihilator diagrams have colimits.

The natural-number diagram of power-annihilator submodules has a colimit, exhibited by the
canonical cocone in `Γ_I(M)`. -/
instance annihilatorHasColimit (I : Ideal R) (M : ModuleCat.{v} R) :
    HasColimit (annihilatorDiagram I M) := ⟨_, annihilatorIsColimit I M⟩

/-- Power-annihilator inclusions agree along index transitions.

For `i ≤ j`, inclusion from `Ann_M(I^i)` to `Ann_M(I^j)` followed by the degree-`j` cocone map
equals the degree-`i` cocone map. -/
lemma annihilator_index_naturality (I : Ideal R) (M : ModuleCat.{v} R)
    {i j : ℕ} (hij : i ≤ j) :
    (annihilatorDiagram I M).map (homOfLE hij) ≫ annihilatorInclusion I M j =
      annihilatorInclusion I M i :=
  (annihilatorCocone I M).w (homOfLE hij)

/-- Module maps preserve annihilation by an ideal power.

If `x ∈ Ann_M(I^n)` and `f : M ⟶ N` is `R`-linear, then `f x ∈ Ann_N(I^n)`. -/
lemma map_mem_powerAnnihilator (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : M) (hx : x ∈ powerAnnihilator I M n) :
    f.hom x ∈ powerAnnihilator I N n := by
  apply (Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) (f.hom x)).mpr
  intro r
  have hr : (r : R) • x = 0 :=
    ((Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) x).mp hx) r
  change (r : R) • f.hom x = 0
  rw [← map_smul, hr, map_zero]

/-- Module morphism induces a map of power-annihilator diagrams.

A module morphism `f : M ⟶ N` restricts to each power-annihilator submodule and gives a
natural transformation of their natural-number diagrams. -/
def annihilatorDiagramMap (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    annihilatorDiagram I M ⟶ annihilatorDiagram I N :=
  DirectedSubmoduleColimit.coefficientDiagramMap
    (powerAnnihilator I M) (powerAnnihilator_monotone I M)
    (powerAnnihilator I N) (powerAnnihilator_monotone I N) f.hom
    (fun n x hx => map_mem_powerAnnihilator I f n x hx)

/-- Power-annihilator diagram map retains the coefficient map's values.

At index `n`, the diagram map induced by `f` sends `x : Ann_M(I^n)` to an element with
underlying value `f(x.val)`. -/
lemma annihilatorDiagramMap_val (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : powerAnnihilator I M n) :
    (((annihilatorDiagramMap I f).app n).hom x).val = f.hom x.val := rfl

/-- Power-annihilator diagrams vary functorially in modules.

The assignment `M ↦ annihilatorDiagram I M` and the restricted maps of module morphisms define
a functor to natural-number diagrams in the module category. -/
def annihilatorDiagramFunctor (I : Ideal R) :
    ModuleCat.{v} R ⥤ (ℕ ⥤ ModuleCat.{v} R) where
  obj := annihilatorDiagram I
  map := annihilatorDiagramMap I
  map_id M := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Power-torsion maps commute with each annihilator cocone map.

For `f : M ⟶ N`, the degree-`n` inclusion into `Γ_I(M)` followed by `Γ_I(f)` equals the
degree-`n` diagram map followed by inclusion into `Γ_I(N)`. -/
lemma annihilator_coefficient_naturality (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    annihilatorInclusion I M n ≫ (functor I).map f =
      (annihilatorDiagramMap I f).app n ≫ annihilatorInclusion I N n := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Power-torsion map is the colimit descent of annihilator maps.

The map `Γ_I(f)` induced by a module morphism equals the unique descent from the source power-
annihilator colimit to the target cocone, after precomposition with the annihilator diagram
transformation. -/
lemma primaryComponentMap_eq_annihilatorDesc (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) :
    (annihilatorIsColimit I M).desc
      ((Cocone.precompose (annihilatorDiagramMap I f)).obj (annihilatorCocone I N)) =
        (functor I).map f := by
  apply (annihilatorIsColimit I M).hom_ext
  intro n
  exact ((annihilatorIsColimit I M).fac _ n).trans
    (annihilator_coefficient_naturality I f n).symm

end ModuleCat.Torsion
