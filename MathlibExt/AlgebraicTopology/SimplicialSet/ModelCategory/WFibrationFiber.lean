/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFiberEdge

/-!
# Strict fibers of weak-equivalence Kan fibrations

Let `f : X → Y` be a Kan fibration between Kan complexes and a Kan-complex weak
equivalence. The map is surjective on vertices. For every vertex `y` of `Y` and
every chosen vertex `x` of the strict fiber over `y`, each based homotopy object
`π_n(fiber_y(f),x)` is a subsingleton, for all `n ≥ 0`.

The strict fiber has the Kan structure inherited from the fibration. These
statements use the given simplicial fiber and its chosen basepoint in the same
simplicial-set universe.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial SSet Limits HomotopicalAlgebra Opposite
open SSet.modelCategoryQuillen

namespace SSet

private lemma pi_map_one_eq_one {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X ⟶ Y) (hf : f.app (op ⦋0⦌) x = y) (n : ℕ) :
    KanComplex.π.map f hf n (1 : KanComplex.π n X x) = 1 := by
  have h1 : (1 : KanComplex.π n X x) =
      KanComplex.π.mk (RelativeMorphism.const : X.PtSimplex n x) := rfl
  rw [h1, KanComplex.π.map_mk]
  have hmap : PtSimplex.map f hf (RelativeMorphism.const : X.PtSimplex n x) =
      (RelativeMorphism.const : Y.PtSimplex n y) := by
    apply RelativeMorphism.ext
    show RelativeMorphism.map (PtSimplex.map f hf
        (RelativeMorphism.const : X.PtSimplex n x)) =
      RelativeMorphism.map (RelativeMorphism.const : Y.PtSimplex n y)
    calc RelativeMorphism.map (PtSimplex.map f hf
          (RelativeMorphism.const : X.PtSimplex n x))
        = RelativeMorphism.map (RelativeMorphism.const : X.PtSimplex n x) ≫ f := rfl
      _ = SSet.const (X := Δ[n]) x ≫ f := rfl
      _ = SSet.const (X := Δ[n]) y := by rw [SSet.const_comp, hf]
      _ = RelativeMorphism.map (RelativeMorphism.const : Y.PtSimplex n y) := rfl
  rw [hmap]
  rfl

private lemma W_bijective_piMap_of_hb {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : KanComplex.W f) {e : X _⦋0⦌} {y : Y _⦋0⦌}
    (hb : f.app (op ⦋0⦌) e = y) (n : ℕ) :
    Function.Bijective (KanComplex.π.map f hb n) := by
  cases hb
  exact KanComplex.W.bijective_piMap hf n e

private lemma fiber_ne_bot_of_vertex {X Y : SSet.{u}} {f : X ⟶ Y}
    (x : X _⦋0⦌) : SSet.Subcomplex.fiber f (f.app (op ⦋0⦌) x) ≠ ⊥ := by
  intro h
  have hmem : x ∈ (SSet.Subcomplex.fiber f (f.app (op ⦋0⦌) x)).obj (op ⦋0⦌) :=
    (SSet.Subcomplex.mem_fiber_obj_zero_iff f _).mpr rfl
  rw [h] at hmem
  simp only [Subfunctor.bot_obj] at hmem
  exact hmem

private lemma exists_vertex_of_fiber_ne_bot {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y _⦋0⦌) (h : SSet.Subcomplex.fiber f y ≠ ⊥) :
    ∃ x : X _⦋0⦌, f.app (op ⦋0⦌) x = y := by
  by_contra hnone
  push Not at hnone
  have h_le : SSet.Subcomplex.fiber f y ≤ ⊥ := by
    intro n x hx
    have h0 : X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op x ∈
        (SSet.Subcomplex.fiber f y).obj (op ⦋0⦌) :=
      (SSet.Subcomplex.fiber f y).map _ hx
    rw [SSet.Subcomplex.mem_fiber_obj_zero_iff] at h0
    exact (hnone _ h0).elim
  exact h (le_antisymm h_le bot_le)

/--
A Kan fibration between Kan complexes which is a Kan-complex weak equivalence
is surjective on vertices: every vertex `y` has a vertex `x` with `f(x) = y`.
-/
theorem KanComplex.W.exists_vertex_over {X Y : SSet.{u}} {f : X ⟶ Y}
    [KanComplex X] [KanComplex Y] [Fibration f]
    (hf : KanComplex.W f) (y : Y _⦋0⦌) :
    ∃ x : X _⦋0⦌, f.app (op ⦋0⦌) x = y := by
  have := hf.isEquivalence_mapFundamentalGroupoid
  obtain ⟨xFG, ⟨isoFG : (SSet.mapFundamentalGroupoid f).obj xFG ≅
      SSet.FundamentalGroupoid.mk y⟩⟩ :=
    Functor.EssSurj.mem_essImage (SSet.mapFundamentalGroupoid f)
      (SSet.FundamentalGroupoid.mk y)
  obtain ⟨x, rfl⟩ : ∃ (x : X _⦋0⦌), xFG = SSet.FundamentalGroupoid.mk x :=
    ⟨(SSet.FundamentalGroupoid.mk_surjective xFG).choose,
      (SSet.FundamentalGroupoid.mk_surjective xFG).choose_spec.symm⟩
  have hObj : (SSet.mapFundamentalGroupoid f).obj (SSet.FundamentalGroupoid.mk x) =
      SSet.FundamentalGroupoid.mk (f.app (op ⦋0⦌) x) := by
    simp [SSet.mapFundamentalGroupoid_obj_mk]
  let iso' : SSet.FundamentalGroupoid.mk (f.app (op ⦋0⦌) x) ≅
      SSet.FundamentalGroupoid.mk y :=
    (eqToIso hObj.symm).trans isoFG
  obtain ⟨e, _⟩ := SSet.FundamentalGroupoid.homMk_surjective iso'.hom
  have hSrc : SSet.Subcomplex.fiber f (f.app (op ⦋0⦌) x) ≠ ⊥ :=
    fiber_ne_bot_of_vertex x
  have hTgt : SSet.Subcomplex.fiber f y ≠ ⊥ :=
    (SSet.Subcomplex.fiber_neq_bot_iff_of_edge f e).mp hSrc
  exact exists_vertex_of_fiber_ne_bot f y hTgt

/--
For a weak-equivalence Kan fibration between Kan complexes, each based homotopy
object `π_n` of a strict fiber is a subsingleton, for every `n ≥ 0` and every
chosen fiber vertex.
-/
theorem subsingleton_π_fiber_of_W_fibration {X Y : SSet.{u}} {f : X ⟶ Y}
    [KanComplex X] [KanComplex Y] [Fibration f] (hf : KanComplex.W f)
    (y : Y _⦋0⦌) (n : ℕ) (x : (SSet.Subcomplex.fiber f y : SSet.{u}) _⦋0⦌) :
    Subsingleton (KanComplex.π n (SSet.Subcomplex.fiber f y : SSet.{u}) x) := by
  have hb : f.app (op ⦋0⦌) x.val = y :=
    (SSet.Subcomplex.mem_fiber_obj_zero_iff f y).mp x.property
  let S : FibrationSequence.{u} := {
    E := X
    B := Y
    p := f
    fibration_p := inferInstance
    fibrant_B := inferInstance
    e := x.val
    b := y
    hb := hb
  }
  have h_pt_eq : S.fiberPoint = x := by
    apply Subtype.ext
    rfl
  have h_sub : Subsingleton (KanComplex.π n S.fiber S.fiberPoint) := by
    constructor
    intro a b
    have h_all_one : ∀ (q : KanComplex.π n S.fiber S.fiberPoint), q = 1 := by
      intro q
      have h_inj : Function.Injective (KanComplex.π.map S.p S.hb n) :=
        (W_bijective_piMap_of_hb hf S.hb n).1
      have h_surj : Function.Surjective (KanComplex.π.map S.p S.hb (n + 1)) :=
        (W_bijective_piMap_of_hb hf S.hb (n + 1)).2
      have h_connect_trivial : ∀ r : KanComplex.π (n + 1) S.B S.b, S.connectingMap n r = 1 := by
        intro r
        obtain ⟨r', hr'⟩ := h_surj r
        rw [← hr']
        exact S.connectingMap_map_eq_one r'
      have h_fiberIncl_one : ∀ q : KanComplex.π n S.fiber S.fiberPoint,
          KanComplex.π.map S.fiberIncl rfl n q = 1 := by
        intro q'
        have h_comp : KanComplex.π.map S.p S.hb n (KanComplex.π.map S.fiberIncl rfl n q') = 1 :=
          S.map_p_comp_fiberIncl_eq_one q'
        have h_one : KanComplex.π.map S.p S.hb n (1 : KanComplex.π n S.E S.e) = 1 :=
          pi_map_one_eq_one S.p S.hb n
        exact h_inj (h_comp.trans h_one.symm)
      obtain ⟨r, hr⟩ := S.exactness_at_fiber q (h_fiberIncl_one q)
      have h_r_one : S.connectingMap n r = 1 := h_connect_trivial r
      rw [← hr, h_r_one]
    have ha := h_all_one a
    have hb_one := h_all_one b
    rw [ha, hb_one]
  exact h_pt_eq ▸ h_sub

end SSet
