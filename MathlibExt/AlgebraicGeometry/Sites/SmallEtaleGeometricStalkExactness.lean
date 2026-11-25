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
# Geometric stalks and local exactness on small étale sites

Categorical exactness uses a common coefficient universe, while local
section predicates refer to the site and its maps. The geometric family
and cover detector are constructed from scheme points and give the local
exactness criterion.
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

/-- An actual common-universe epimorphism has original section lifts on an
actual cover. Stalk surjectivity comes from the stock stalk left adjoint. -/
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

/-- The last-map epimorphism is equivalent to the original local lift
condition, without any common-universe W-equals-local-bijective premise. -/
theorem smallEtaleCommon_epi_iff_locallySurjective (b : F ⟶ G) :
    Epi b ↔ Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom := by
  constructor
  · intro hb
    let := hb
    exact smallEtaleCommon_epi_locallySurjective b
  · intro hb
    let := hb
    exact Sheaf.epi_of_isLocallySurjective b

/-- The full categorical criterion is exactly literal component injectivity,
range=zero-kernel and actual local lifts of every original section. -/
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

/-- The actual stock filtered colimit over the original geometric
neighborhoods, retaining the original scheme and coefficient universes. -/
abbrev smallEtaleCommonGeometricStalk (x : Spec (.of Ω) ⟶ X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} ⥤ AddCommGrpCat.{max u w} :=
  (smallEtaleGeometricPointCommon.{u, w} x).sheafFiber

/-- Its object is literally the colimit of the original neighborhood sections. -/
theorem smallEtaleCommonGeometricStalk_obj (x : Spec (.of Ω) ⟶ X)
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleCommonGeometricStalk.{u, w} x).obj Q =
      colimit ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w} x).fiber).op ⋙ Q.obj) :=
  rfl

/-- Its morphism is the actual induced colimit map of the original components. -/
theorem smallEtaleCommonGeometricStalk_map (x : Spec (.of Ω) ⟶ X)
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (a : Q ⟶ Q') :
    (smallEtaleCommonGeometricStalk.{u, w} x).map a =
      colim.map (((Functor.whiskeringLeft _ _ _).obj
        ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w} x).fiber).op)).map a.hom) :=
  rfl

/-- Actual common geometric stalks preserve exactness, and their original
canonical family detects it by the stock conservative-exact-functor theorem. -/
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

/-- Both complete exactness criteria use the same original maps and the
actual common-universe geometric stalk construction. -/
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
