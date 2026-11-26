/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local short exact sequences on a small étale site

Let X be a scheme in universe u and F′→F→F″ sheaves of abelian groups with coefficient universe
w independent of u. Local short exactness means that on every étale object U the first section
map is injective and its image is the kernel of the second. Every section c of F″(U) must also
lift locally: there is a covering sieve on U such that, along each arrow V→U of that sieve, the
restriction of c is the image of a section of F(V).

The local-lifting condition is equivalent to local surjectivity of the presheaf map F→F″.
Image–kernel equality supplies the zero composite, so the two maps form a short complex. A
morphism between these sequences consists of three sheaf maps satisfying the two commuting
squares. The definition requires no abelian-category structure on the sheaf category in the
coefficient universe.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {X : Scheme.{u}}
  {F' F F'' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
  (a : F' ⟶ F) (b : F ⟶ F'')

/-- Let X be a scheme in universe u and F′,F,F″ abelian-group sheaves on its small étale site with
coefficient carriers in an independent universe w. Let a:F′→F and b:F→F″. This condition
requires a_U injective and image(a_U)=ker(b_U) for every étale U over X. For every c∈F″(U),
there is a covering sieve S on U such that for each p:V→U in S a section d∈F(V) satisfies
b_V(d)=F″(p)(c). The cover is a sieve of all its arrows, with no finite-cover requirement. -/
def originalSmallEtaleLocalShortExact : Prop :=
  (∀ U : X.Etale, Function.Injective (a.hom.app (op U))) ∧
  (∀ U : X.Etale, Set.range (a.hom.app (op U)) =
    {x | b.hom.app (op U) x = 0}) ∧
  ∀ (U : X.Etale) (c : F''.obj.obj (op U)),
    ∃ R : Sieve U, R ∈ X.smallEtaleTopology U ∧
      ∀ (V : X.Etale) (p : V ⟶ U), R p →
        ∃ d : F.obj.obj (op V), b.hom.app (op V) d = F''.obj.map p.op c

variable {a b}

/-- Let X be a scheme in universe u and F′,F,F″ abelian-group sheaves on its small étale site with
coefficient carriers in an independent universe w. Let a:F′→F and b:F→F″. If a,b satisfy the
sectionwise injectivity, image–kernel equality and covering-sieve lifting condition, then b is
locally surjective for the small étale topology. Each section of F″ becomes an image after
restriction along the arrows of a covering sieve. -/
theorem originalSmallEtaleLocalShortExact_locallySurjective
    (h : originalSmallEtaleLocalShortExact a b) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom where
  imageSieve_mem {U} c := by
    obtain ⟨R, hR, hlift⟩ := h.2.2 U c
    exact X.smallEtaleTopology.superset_covering
      (fun V p hp => hlift V p hp) hR

/-- Let X be a scheme in universe u and F′,F,F″ abelian-group sheaves on its small étale site with
coefficient carriers in an independent universe w. Let a:F′→F and b:F→F″. The covering-sieve
definition is equivalent to a_U injective and image(a_U)=ker(b_U) for every étale U, together
with local surjectivity of b as a presheaf map. The image sieve of a target section gives the
covering sieve in the reverse implication. -/
theorem originalSmallEtaleLocalShortExact_iff :
    originalSmallEtaleLocalShortExact a b ↔
      (∀ U : X.Etale, Function.Injective (a.hom.app (op U))) ∧
      (∀ U : X.Etale, Set.range (a.hom.app (op U)) =
        {x | b.hom.app (op U) x = 0}) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, originalSmallEtaleLocalShortExact_locallySurjective h⟩
  · rintro ⟨hinj, hexact, hsurj⟩
    let := hsurj
    refine ⟨hinj, hexact, ?_⟩
    intro U c
    exact ⟨Presheaf.imageSieve b.hom c,
      Presheaf.imageSieve_mem X.smallEtaleTopology b.hom c, fun V p hp => hp⟩

/-- Let X be a scheme in universe u and F′,F,F″ abelian-group sheaves on its small étale site with
coefficient carriers in an independent universe w. Let a:F′→F and b:F→F″. For a locally short
exact sequence, a≫b=0 as a sheaf morphism. At each U, every element in the image of a_U belongs
to ker(b_U), giving the pointwise zero composite. -/
theorem originalSmallEtaleLocalShortExact_comp_eq_zero
    (h : originalSmallEtaleLocalShortExact a b) : a ≫ b = 0 := by
  ext U x
  have hx : a.hom.app U x ∈ Set.range (a.hom.app U) := ⟨x, rfl⟩
  rw [h.2.1 U.unop] at hx
  exact hx

/-- Let X be a scheme in universe u and F′,F,F″ abelian-group sheaves on its small étale site with
coefficient carriers in an independent universe w. Let a:F′→F and b:F→F″. Given local short
exactness, the image–kernel equality gives a≫b=0. This defines the short complex F′ --a→ F --b→
F″ in the sheaf category, with these maps and their derived zero composite in the same
coefficient universe. -/
def originalSmallEtaleLocalShortComplex
    (h : originalSmallEtaleLocalShortExact a b) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :=
  ShortComplex.mk a b (originalSmallEtaleLocalShortExact_comp_eq_zero h)

/-- Let X be a scheme in universe u and F′,F,F″ abelian-group sheaves on its small étale site with
coefficient carriers in an independent universe w. Let a:F′→F and b:F→F″. For another locally
short exact G′ --a′→ G --b′→ G″, a morphism consists of sheaf maps f′:F′→G′, f:F→G and f″:F″→G″
satisfying a≫f=f′≫a′ and b≫f″=f≫b′. It is the morphism of the associated short complexes. -/
abbrev OriginalSmallEtaleLocalShortExactHom
    (h : originalSmallEtaleLocalShortExact a b)
    {G' G G'' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
    {a' : G' ⟶ G} {b' : G ⟶ G''}
    (h' : originalSmallEtaleLocalShortExact a' b') :=
  originalSmallEtaleLocalShortComplex h ⟶ originalSmallEtaleLocalShortComplex h'

end AlgebraicGeometry.Scheme.DerivedSections
