/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricPointsCommonUniverse
public import MathlibExt.CategoryTheory.Sites.AbelianExactness
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Stalk and local section criteria for small étale exactness

For abelian sheaves with coefficient universe `max u w`, a morphism is an epimorphism
precisely when its sections are locally surjective for the small étale topology.

A short complex is short exact precisely when its first map is injective on each étale object,
its sectionwise image equals the kernel of the second map, and every section of the last sheaf
lifts after restriction along a covering sieve. Equivalently, its image under every geometric
stalk functor over a separably closed field in universe `u` is short exact.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {X : Scheme.{u}}
  {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}

/-- Stalkwise surjectivity over the actual canonical geometric family gives
original local lifts. Equality of two germs is refined on an actual common
neighborhood before applying the actual cover detector. -/
private theorem locallySurjective_of_common_stalks (b : F ⟶ G)
    (hsurj : ∀ (Φ : (smallEtaleCanonicalGeometricPointsCommon.{u, w} X).FullSubcategory),
      Function.Surjective (Φ.obj.presheafFiber.map b.hom)) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom where
  imageSieve_mem {U} c := by
    apply smallEtaleCanonicalGeometricPointsCommon_cover.{u, w}
    intro Φ z
    let φ := Φ.obj
    obtain ⟨t, ht⟩ := hsurj Φ (φ.toPresheafFiber U z G.obj c)
    obtain ⟨V, y, d, hd⟩ := φ.toPresheafFiber_jointly_surjective t
    obtain ⟨W, ⟨g, hg⟩, ⟨p, hp⟩, _⟩ :=
      IsCofilteredOrEmpty.cone_objs (φ.fiber.elementsMk V y) (φ.fiber.elementsMk U z)
    have hnat : b.hom.app (op W.1) (F.obj.map g.op d) =
        G.obj.map g.op (b.hom.app (op V) d) :=
      b.hom.naturality_apply g.op d
    have heq :
        φ.toPresheafFiber W.1 W.2 G.obj (b.hom.app (op W.1) (F.obj.map g.op d)) =
          φ.toPresheafFiber W.1 W.2 G.obj (G.obj.map p.op c) := by
      calc
        _ = φ.toPresheafFiber W.1 W.2 G.obj (G.obj.map g.op (b.hom.app (op V) d)) :=
          congrArg _ hnat
        _ = φ.toPresheafFiber V (φ.fiber.map g W.2) G.obj (b.hom.app (op V) d) := by
          rw [φ.toPresheafFiber_w_apply]
        _ = φ.toPresheafFiber V y G.obj (b.hom.app (op V) d) := by rw [hg]
        _ = φ.presheafFiber.map b.hom (φ.toPresheafFiber V y F.obj d) :=
          (φ.toPresheafFiber_naturality_apply b.hom V y d).symm
        _ = φ.presheafFiber.map b.hom t := by rw [hd]
        _ = φ.toPresheafFiber U z G.obj c := ht
        _ = φ.toPresheafFiber W.1 W.2 G.obj (G.obj.map p.op c) := by
          rw [φ.toPresheafFiber_w_apply, hp]
    obtain ⟨T, q, v, hq, hlocal⟩ :=
      (φ.toPresheafFiber_eq_iff' W.1 W.2 _ _).mp heq
    refine ⟨T, q ≫ p, ?_, v, ?_⟩
    · refine ⟨F.obj.map q.op (F.obj.map g.op d), ?_⟩
      calc
        b.hom.app (op T) (F.obj.map q.op (F.obj.map g.op d)) =
            G.obj.map q.op (b.hom.app (op W.1) (F.obj.map g.op d)) :=
          b.hom.naturality_apply q.op _
        _ = G.obj.map q.op (G.obj.map p.op c) := hlocal
        _ = G.obj.map (q ≫ p).op c := by simp
    · change φ.fiber.map (q ≫ p) v = z
      rw [Functor.map_comp, ConcreteCategory.comp_apply, hq]
      exact hp

/-- Epimorphisms of abelian sheaves are locally surjective.

An epimorphism of common-universe small étale abelian sheaves is locally surjective on
sections. -/
theorem smallEtaleCommon_epi_locallySurjective (b : F ⟶ G) [Epi b] :
    Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom := by
  apply locallySurjective_of_common_stalks b
  intro Φ
  let : Functor.PreservesEpimorphisms (Φ.obj.sheafFiber (A := AddCommGrpCat.{max u w})) :=
    Functor.preservesEpimorphisms_of_adjunction
      (Φ.obj.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w}))
  have hmap : Epi ((Φ.obj.sheafFiber (A := AddCommGrpCat.{max u w})).map b) :=
    (Φ.obj.sheafFiber (A := AddCommGrpCat.{max u w})).map_epi b
  exact (AddCommGrpCat.epi_iff_surjective _).mp hmap

/-- Local surjectivity characterizes sheaf epimorphisms.

A morphism of common-universe small étale abelian sheaves is epi if and only if its presheaf
section maps are locally surjective. -/
theorem smallEtaleCommon_epi_iff_locallySurjective (b : F ⟶ G) :
    Epi b ↔ Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom := by
  constructor
  · intro hb
    let := hb
    exact smallEtaleCommon_epi_locallySurjective b
  · intro hb
    let := hb
    exact Sheaf.epi_of_isLocallySurjective b

/-- Local section criterion for a short exact sheaf sequence.

Short exactness is equivalent to sectionwise injectivity of the first map, equality of its
range with the second map's kernel on each étale object, and local lifting of every last-sheaf
section along a covering sieve. -/
theorem smallEtaleCommon_shortExact_iff_local
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})) :
    S.ShortExact ↔
      (∀ U : X.Etale, Function.Injective (S.f.hom.app (op U))) ∧
      (∀ U : X.Etale, Set.range (S.f.hom.app (op U)) =
        {x | S.g.hom.app (op U) x = 0}) ∧
      ∀ (U : X.Etale) (c : S.X₃.obj.obj (op U)),
        ∃ R : Sieve U, R ∈ X.smallEtaleTopology U ∧
          ∀ (V : X.Etale) (p : V ⟶ U), R p →
            ∃ d : S.X₂.obj.obj (op V), S.g.hom.app (op V) d = S.X₃.obj.map p.op c := by
  constructor
  · intro hS
    have hleft := S.sheaf_exact_mono_iff_components.mp ⟨hS.exact, hS.mono_f⟩
    let := hS.epi_g
    let := smallEtaleCommon_epi_locallySurjective S.g
    refine ⟨hleft.1, hleft.2, ?_⟩
    intro U c
    exact ⟨Presheaf.imageSieve S.g.hom c,
      Presheaf.imageSieve_mem X.smallEtaleTopology S.g.hom c, fun V p hp => hp⟩
  · rintro ⟨hinj, hexact, hlocal⟩
    have hleft := S.sheaf_exact_mono_iff_components.mpr ⟨hinj, hexact⟩
    have hsurj : Presheaf.IsLocallySurjective X.smallEtaleTopology S.g.hom := {
      imageSieve_mem := by
        intro U c
        obtain ⟨R, hR, hlift⟩ := hlocal U c
        exact X.smallEtaleTopology.superset_covering (fun V p hp => hlift V p hp) hR }
    exact ShortComplex.ShortExact.mk' hleft.1 hleft.2
      ((smallEtaleCommon_epi_iff_locallySurjective S.g).mpr hsurj)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Geometric stalk functor for common universe coefficients.

For `Spec Ω → X` with `Ω` separably closed in universe `u`, take the sheaf-fiber functor of
its common-universe geometric point. -/
abbrev smallEtaleCommonGeometricStalk (x : Spec (.of Ω) ⟶ X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} ⥤ AddCommGrpCat.{max u w} :=
  (smallEtaleGeometricPointCommon.{u, w} x).sheafFiber

/-- Geometric stalk as a filtered neighborhood colimit.

The stalk of a sheaf is the colimit of its sections over the opposite elements category of the
lifted geometric fiber. -/
theorem smallEtaleCommonGeometricStalk_obj (x : Spec (.of Ω) ⟶ X)
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleCommonGeometricStalk.{u, w} x).obj Q =
      colimit ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w} x).fiber).op ⋙ Q.obj) :=
  rfl

/-- Geometric stalk morphism is the map on neighborhood colimits.

A sheaf morphism acts on geometric stalks by the colimit map of its section components over
geometric neighborhoods. -/
theorem smallEtaleCommonGeometricStalk_map (x : Spec (.of Ω) ⟶ X)
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (a : Q ⟶ Q') :
    (smallEtaleCommonGeometricStalk.{u, w} x).map a =
      colim.map (((Functor.whiskeringLeft _ _ _).obj
        ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w} x).fiber).op)).map a.hom) :=
  rfl

/-- Geometric stalks detect short exactness.

A common-universe sheaf short complex is short exact if and only if its image at every
geometric point over a separably closed field in universe `u` is short exact. -/
theorem smallEtaleCommon_shortExact_iff_geometricStalks
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})) :
    S.ShortExact ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        (S.map (smallEtaleCommonGeometricStalk.{u, w} x)).ShortExact := by
  constructor
  · intro hS Ω _ _ x
    let := hS.mono_f
    let := hS.epi_g
    exact hS.map (smallEtaleCommonGeometricStalk.{u, w} x)
  · intro hS
    have hP :=
      (smallEtaleCanonicalGeometricPointsCommon_conservative.{u, w} X).jointlyReflectIsomorphisms
        AddCommGrpCat.{max u w}
    apply (hP.shortExact_iff S).mpr
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
    subst Φ
    exact hS _ (smallEtaleCanonicalGeometricMorphism X x)

/-- Stalk and local section exactness criteria agree.

For a sheaf short complex, short exactness is equivalent both to exactness at every geometric
stalk and to the sectionwise kernel and local-surjectivity conditions. -/
theorem original_small_etale_geometric_stalk_exactness
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})) :
    (S.ShortExact ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        (S.map (smallEtaleCommonGeometricStalk.{u, w} x)).ShortExact) ∧
    (S.ShortExact ↔
      (∀ U : X.Etale, Function.Injective (S.f.hom.app (op U))) ∧
      (∀ U : X.Etale, Set.range (S.f.hom.app (op U)) =
        {x | S.g.hom.app (op U) x = 0}) ∧
      ∀ (U : X.Etale) (c : S.X₃.obj.obj (op U)),
        ∃ R : Sieve U, R ∈ X.smallEtaleTopology U ∧
          ∀ (V : X.Etale) (p : V ⟶ U), R p →
            ∃ d : S.X₂.obj.obj (op V), S.g.hom.app (op V) d = S.X₃.obj.map p.op c) :=
  ⟨smallEtaleCommon_shortExact_iff_geometricStalks S, smallEtaleCommon_shortExact_iff_local S⟩

end AlgebraicGeometry.Scheme.DerivedSections
