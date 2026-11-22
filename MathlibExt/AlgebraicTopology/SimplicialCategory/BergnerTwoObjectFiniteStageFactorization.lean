/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredBergnerHomCompactness
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerPointPresentability
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectGenerators

/-!
# Whole original two-object maps factor through actual filtered C0 stages

Both original object images are found in one actual filtered stage.
Finite presentability factors the entire original forward Hom through
the genuine original tail-Hom colimit. The existing two-object
constructor and its full readback give the same whole original functor,
including coincident target images and every scalar operator.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.BergnerTwoObject

private theorem eq_of_forward {K : SSet.{u}} {D : Type v} [EnrichedCategory SSet.{u} D]
    (F G : EnrichedFunctor SSet.{u} (object K) D)
    (hs : F.obj (source K) = G.obj (source K))
    (ht : F.obj (target K) = G.obj (target K))
    (hm : F.map (source K) (target K) ≫
      eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y) hs ht) =
        G.map (source K) (target K)) : F = G := by
  let e := fixedEndpointsEquiv (X := K) (G.obj (source K)) (G.obj (target K))
  have h : e ⟨F, hs, ht⟩ = e ⟨G, rfl, rfl⟩ :=
    hm.trans (Category.comp_id _).symm
  exact congrArg Subtype.val (e.injective h)

private theorem forward_transport {A B C D X : SSet.{u}}
    (n : X ⟶ A) (p : A ⟶ B) (k : X ⟶ D)
    (t : B = C) (q : C = D) (r : B = D)
    (h : n ≫ (p ≫ eqToHom t) = k ≫ eqToHom q.symm) :
    (n ≫ p) ≫ eqToHom r = k := by
  cases t
  cases q
  simpa only [eqToHom_refl, Category.comp_id] using h

/-- Every whole original compact two-object map factors through an actual original filtered C0 stage. -/
theorem whole_map_factor {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Carrier.{u}) (s : Cocone F) (hs : IsColimit s)
    (hC : ∀ {i j : J} (f : i ⟶ j), Bergner.cofibrations (F.map f))
    (K : SSet.{u}) [IsFinitelyPresentable.{u} K] (G : object K ⟶ s.pt) :
    ∃ (j : J) (H : object K ⟶ F.obj j), H ≫ s.ι.app j = G := by
  have hObj := isColimitOfPreserves forgetObjects.{u} hs
  obtain ⟨j, x, y, hx, hy⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ hObj
      (G.obj (source K)) (G.obj (target K))
  let m : K ⟶ (s.ι.app j).obj x ⟶[SSet.{u}] (s.ι.app j).obj y :=
    G.map (source K) (target K) ≫
      eqToHom (congrArg₂ (fun a b : s.pt => a ⟶[SSet.{u}] b) hx.symm hy.symm)
  obtain ⟨a, n, hn⟩ := OriginalFilteredUnderHom.hom_factor F s hs hC j x y K m
  let H : object K ⟶ F.obj a.right :=
    ofMap ((F.map a.hom).obj x) ((F.map a.hom).obj y) n
  have ha : (s.ι.app a.right).obj ((F.map a.hom).obj x) = (s.ι.app j).obj x :=
    congrArg (fun R : F.obj j ⟶ s.pt => R.obj x) (s.w a.hom)
  have hb : (s.ι.app a.right).obj ((F.map a.hom).obj y) = (s.ι.app j).obj y :=
    congrArg (fun R : F.obj j ⟶ s.pt => R.obj y) (s.w a.hom)
  have hSrc : (H ≫ s.ι.app a.right).obj (source K) = G.obj (source K) := ha.trans hx
  have hTgt : (H ≫ s.ι.app a.right).obj (target K) = G.obj (target K) := hb.trans hy
  refine ⟨a.right, H, eq_of_forward (H ≫ s.ι.app a.right) G hSrc hTgt ?_⟩
  change n ≫ ((s.ι.app a.right).map ((F.map a.hom).obj x) ((F.map a.hom).obj y) ≫
    eqToHom (congrArg₂ (fun b c : s.pt => b ⟶[SSet.{u}] c) ha hb)) = m at hn
  exact forward_transport n
    ((s.ι.app a.right).map ((F.map a.hom).obj x) ((F.map a.hom).obj y))
    (G.map (source K) (target K))
    (congrArg₂ (fun b c : s.pt => b ⟶[SSet.{u}] c) ha hb)
    (congrArg₂ (fun b c : s.pt => b ⟶[SSet.{u}] c) hx hy)
    (congrArg₂ (fun b c : s.pt => b ⟶[SSet.{u}] c) hSrc hTgt) hn

end CategoryTheory.SimplicialEnrichment.BergnerTwoObject
