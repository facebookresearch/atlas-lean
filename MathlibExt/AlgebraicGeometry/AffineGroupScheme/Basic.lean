/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/AlgebraicGeometry/AffineGroupScheme/Basic.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The category of affine group schemes over `Spec S`

This file introduces the category of affine group schemes over `Spec S` for a commutative ring `S` —
the full subcategory of group objects in schemes over `Spec S` whose underlying scheme is affine —
together with the `Γ`-direction endpoint of the dictionary between affine group schemes and
commutative Hopf algebras, stated for a plain-typed base ring `R` and an arbitrary structure
morphism rather than through `Scheme.Over` instance data: a commutative `R`-Hopf algebra structure
on the global sections of an affine group scheme `φ : G ⟶ Spec R` (`hopfAlgebraGamma`).

The `Spec`-direction endpoint — the group-object structure on `Spec A` over `Spec R`
for a commutative `R`-Hopf algebra `A` — needs no declaration here: it is Mathlib's
`AlgebraicGeometry.instGrpObjSpecAsOverSpec`, and its `Over.mk` spelling is reached by
`inferInstanceAs (GrpObj ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))))`
at any use site. Everything consumes the instances of Mathlib's
`AlgebraicGeometry/Group/Affine.lean`.
Affineness enters only as the object property cutting out the full subcategory;
further refinements stay predicates rather than being baked into the category. The
anti-equivalence with commutative `S`-Hopf algebras is in
`MathlibExt/AlgebraicGeometry/AffineGroupScheme/Equivalence.lean`.
-/

public section

namespace MathlibExt

open CategoryTheory AlgebraicGeometry Scheme Opposite

universe u

/-- The object property on group objects in schemes over `Spec S` selecting those whose
underlying scheme is affine. Over the affine base `Spec S` this is equivalent to the
structure morphism being an affine morphism; over a general base scheme only the
relative notion is correct, so this property must not be transplanted verbatim there. -/
def affineGroupSchemeProperty (S : CommRingCat.{u}) : ObjectProperty (Grp (Over (Spec S))) :=
  fun G => IsAffine G.X.left

/-- Membership in the affine-group-scheme object property. -/
@[simp]
lemma affineGroupSchemeProperty_iff {S : CommRingCat.{u}} (G : Grp (Over (Spec S))) :
    affineGroupSchemeProperty S G ↔ IsAffine G.X.left := Iff.rfl

/-- The category of affine group schemes over `Spec S`: the full subcategory of group
objects in schemes over `Spec S` whose underlying scheme is affine. -/
abbrev AffineGroupSchemeCat (S : CommRingCat.{u}) : Type _ :=
  (affineGroupSchemeProperty S).FullSubcategory

/-- Being an affine group scheme is invariant under isomorphism of group objects: an
isomorphism induces an isomorphism of underlying schemes, and affineness transfers
along it. -/
instance (S : CommRingCat.{u}) : (affineGroupSchemeProperty S).IsClosedUnderIsomorphisms where
  of_iso e hG :=
    (IsAffine.iff_of_isIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom).mp hG

/-- Membership in `AffineGroupSchemeCat` supplies affineness of the underlying scheme
automatically, so downstream instance searches need not invoke `property` by hand. -/
instance {S : CommRingCat.{u}} (G : AffineGroupSchemeCat S) : IsAffine G.obj.X.left := G.property

variable {R : Type u} [CommRing R]

/-- Mathlib's Hopf-algebra structure on the global sections of an affine group scheme,
applied at a bundled ring `S : CommRingCat` bound as a variable. Private elaboration
shim, not API: the carrier `↥(CommRingCat.of R)` reduces to `R` before instance
synthesis, after which unification cannot match the bundled instance head, so the
plain-typed goal of `hopfAlgebraGamma` cannot find the instance directly and inlining
this application there fails to elaborate; only the explicitly applied bundled-`S`
form survives, with definitional unfolding closing the gap on application. -/
@[instance_reducible] private noncomputable def hopfAlgebraGammaAux
    (S : CommRingCat.{u}) (G : Scheme.{u})
    [G.Over (Spec S)] [GrpObj (G.asOver (Spec S))] [IsAffine G] : HopfAlgebra S (Γ.obj (op G)) :=
  inferInstanceAs (HopfAlgebra S Γ(G, ⊤))

/-- The global sections of an affine group scheme `φ : G ⟶ Spec R` are a commutative `R`-Hopf
algebra. This is the `Γ`-direction endpoint of the dictionary between affine group schemes and
commutative Hopf algebras, stated for an arbitrary structure morphism `φ` with the group structure
carried by the object `Over.mk φ` of schemes over `Spec R` — a statement Mathlib's
`Scheme.Over`-instance form cannot express directly. Not an instance, because `φ` is data that
instance search cannot recover from the goal. -/
@[instance_reducible] noncomputable def hopfAlgebraGamma {G : Scheme.{u}}
    (φ : G ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk φ)] [IsAffine G] :
    HopfAlgebra R (Γ.obj (op G)) :=
  letI : G.Over (Spec (CommRingCat.of R)) := ⟨φ⟩
  letI : GrpObj (G.asOver (Spec (CommRingCat.of R))) := ‹GrpObj (Over.mk φ)›
  hopfAlgebraGammaAux (CommRingCat.of R) G

end MathlibExt
