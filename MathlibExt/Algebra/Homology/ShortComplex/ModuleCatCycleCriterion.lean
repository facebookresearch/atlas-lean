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

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso

/-!
# Quasi-isomorphisms from cycle classes of module short complexes

Let R be an arbitrary ring and φ:S → T a morphism of short complexes of
R-modules. If every cycle y of T has a cycle x of S with
[φ₂(x)]=[y] in T₂/Im(T.f), the induced homology map is surjective.
If a cycle x of S whose image class vanishes also has [x]=0 in
S₂/Im(S.f), that homology map is injective.
Together these conditions make φ a quasi-isomorphism. The ring and
module-carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe u v

variable {R : Type u} [Ring R]

private def liftCycle (S : ShortComplex (ModuleCat.{v} R))
    (x : S.X₂) (hx : S.g.hom x = 0) : S.cycles :=
  S.moduleCatCyclesIso.inv.hom ⟨x, hx⟩

private theorem liftCycle_value (S : ShortComplex (ModuleCat.{v} R))
    (x : S.X₂) (hx : S.g.hom x = 0) :
    S.iCycles.hom (liftCycle S x hx) = x := by
  with_unfolding_all exact
    (congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f.hom ⟨x, hx⟩)
      S.moduleCatCyclesIso_inv_iCycles)

private theorem projection_class (S : ShortComplex (ModuleCat.{v} R))
    (x : S.cycles) :
    S.homologyι.hom (S.homologyπ.hom x) = S.pOpcycles.hom (S.iCycles.hom x) := by
  with_unfolding_all exact congrArg (fun f => f.hom x) S.homology_π_ι

private theorem mapped_class {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (x : S.cycles) :
    T.homologyι.hom ((ShortComplex.homologyMap φ).hom (S.homologyπ.hom x)) =
      T.pOpcycles.hom (φ.τ₂.hom (S.iCycles.hom x)) := by
  with_unfolding_all exact
    (congrArg (fun f : S.cycles ⟶ T.opcycles => f.hom x)
      (ShortComplex.π_homologyMap_ι φ))

/-- Let R be an arbitrary ring and φ:S → T a morphism of short complexes
of independently sized R-modules. Assume every y∈T₂ with T.g(y)=0
admits x∈S₂ with S.g(x)=0 and [φ₂(x)]=[y] in T₂/Im(T.f).
Assume also that S.g(x)=0 and [φ₂(x)]=0 imply [x]=0 in S₂/Im(S.f).
Then the canonical homology map of φ is an isomorphism, so φ is a
quasi-isomorphism of short complexes. -/
theorem moduleCat_quasiIso_of_cycle_classes {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hLift : ∀ y : T.X₂, T.g.hom y = 0 →
      ∃ (x : S.X₂) (_hx : S.g.hom x = 0),
        T.pOpcycles.hom (φ.τ₂.hom x) = T.pOpcycles.hom y)
    (hDetect : ∀ x : S.X₂, S.g.hom x = 0 →
      T.pOpcycles.hom (φ.τ₂.hom x) = 0 → S.pOpcycles.hom x = 0) :
    ShortComplex.QuasiIso φ := by
  let g := ShortComplex.homologyMap φ
  have hZero (a : S.homology) (ha : g.hom a = 0) : a = 0 := by
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
    let x := S.iCycles.hom z
    have hx : S.g.hom x = 0 := by
      with_unfolding_all exact congrArg (fun f => f.hom z) S.iCycles_g
    have hMapped : T.pOpcycles.hom (φ.τ₂.hom x) = 0 := by
      calc
        T.pOpcycles.hom (φ.τ₂.hom x) =
            T.homologyι.hom (g.hom (S.homologyπ.hom z)) := (mapped_class φ z).symm
        _ = T.homologyι.hom (g.hom a) := congrArg (fun b => T.homologyι.hom (g.hom b)) hz
        _ = 0 := (congrArg T.homologyι.hom ha).trans T.homologyι.hom.map_zero
    have hClass := hDetect x hx hMapped
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    calc
      S.homologyι.hom a = S.homologyι.hom (S.homologyπ.hom z) :=
        congrArg S.homologyι.hom hz.symm
      _ = S.pOpcycles.hom x := projection_class S z
      _ = 0 := hClass
      _ = S.homologyι.hom 0 := S.homologyι.hom.map_zero.symm
  have hInjective : Function.Injective g.hom := by
    intro a b hab
    have hDiff : g.hom (a - b) = 0 := by
      rw [g.hom.map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hZero (a - b) hDiff)
  have hSurjective : Function.Surjective g.hom := by
    intro a
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance a
    let y := T.iCycles.hom z
    have hy : T.g.hom y = 0 := by
      with_unfolding_all exact congrArg (fun f => f.hom z) T.iCycles_g
    obtain ⟨x, hx, hClass⟩ := hLift y hy
    let w := liftCycle S x hx
    refine ⟨S.homologyπ.hom w, ?_⟩
    apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
    calc
      T.homologyι.hom (g.hom (S.homologyπ.hom w)) =
          T.pOpcycles.hom (φ.τ₂.hom (S.iCycles.hom w)) := mapped_class φ w
      _ = T.pOpcycles.hom (φ.τ₂.hom x) :=
        congrArg (fun b => T.pOpcycles.hom (φ.τ₂.hom b)) (liftCycle_value S x hx)
      _ = T.pOpcycles.hom y := hClass
      _ = T.homologyι.hom (T.homologyπ.hom z) := (projection_class T z).symm
      _ = T.homologyι.hom a := congrArg T.homologyι.hom hz
  exact (ShortComplex.quasiIso_iff φ).mpr
    ((ConcreteCategory.isIso_iff_bijective g).mpr ⟨hInjective, hSurjective⟩)


end CategoryTheory.ShortComplex
