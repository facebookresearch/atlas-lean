/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.TorsionModP

@[expose] public section

open CategoryTheory

open scoped Pointwise

namespace Rep

/-- Consumer with the original binders: a finite integral representation
of a finite group, in universe zero. -/
private theorem exactSource {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hG : (Nat.card G).Coprime p) (A : Rep.{0} ℤ G) [Finite A] :
    Nonempty (repTorsionP p A ≅ repModP p A) :=
  nonempty_repTorsionP_iso_repModP p hG A

/-- Higher-universe consumer: the group and the carrier may live in
universe one. -/
private theorem exactSource_univ {G : Type 1} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] (hG : (Nat.card G).Coprime p) (A : Rep.{1} ℤ G)
    [Finite A] : Nonempty (repTorsionP p A ≅ repModP p A) :=
  nonempty_repTorsionP_iso_repModP p hG A

/-- Boundary example: finiteness of the carrier matters. For the trivial
integral representation on `ℤ`, the `2`-torsion is zero while the mod-`2`
reduction is not, so the two are not isomorphic. -/
private theorem boundary_finite_matters :
    ¬ Nonempty (repTorsionP 2
        (Rep.of (Representation.trivial ℤ Unit ℤ)) ≅
      repModP 2 (Rep.of (Representation.trivial ℤ Unit ℤ))) := by
  intro h
  obtain ⟨i⟩ := h
  have e := (forget (Rep (ZMod 2) Unit)).mapIso i
  have hsub : Subsingleton (repTorsionP 2
      (Rep.of (Representation.trivial ℤ Unit ℤ))) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (2 : ℤ) • (x : ℤ) = 0 :=
      (Submodule.mem_torsionBy_iff (2 : ℤ) (x : ℤ)).1 x.2
    have hy : (2 : ℤ) • (y : ℤ) = 0 :=
      (Submodule.mem_torsionBy_iff (2 : ℤ) (y : ℤ)).1 y.2
    change (2 : ℤ) * (x : ℤ) = 0 at hx
    change (2 : ℤ) * (y : ℤ) = 0 at hy
    have hx0 : (x : ℤ) = 0 := by
      rcases Int.mul_eq_zero.1 hx with h | h
      · norm_num at h
      · exact h
    have hy0 : (y : ℤ) = 0 := by
      rcases Int.mul_eq_zero.1 hy with h | h
      · norm_num at h
      · exact h
    rw [hx0, hy0]
  have hne : (Submodule.Quotient.mk (1 : ℤ) :
      repModP 2 (Rep.of (Representation.trivial ℤ Unit ℤ))) ≠
      Submodule.Quotient.mk 0 := by
    intro hcon
    have hmem : (1 : ℤ) ∈ (2 : ℤ) • (⊤ : Submodule ℤ ℤ) := by
      exact (Submodule.Quotient.mk_eq_zero
        ((2 : ℤ) • (⊤ : Submodule ℤ ℤ))).1 hcon
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hmem
    change (2 : ℤ) * y = 1 at hy
    omega
  have h01 := hsub.elim (e.inv (Submodule.Quotient.mk (1 : ℤ)))
    (e.inv (Submodule.Quotient.mk (0 : ℤ)))
  have h01' : e.toEquiv.symm (Submodule.Quotient.mk (1 : ℤ)) =
      e.toEquiv.symm (Submodule.Quotient.mk (0 : ℤ)) := h01
  have h2 := congrArg e.toEquiv h01'
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  exact hne h2

-- With `k = ZMod p`, instance search still finds Mathlib's module structures on the quotient by
-- `p • ⊤` and on the `p`-torsion submodule: the reduction module adds no competing instance.
example {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] :
    (inferInstance : Module (ZMod p) (V ⧸ ((p : ZMod p) • (⊤ : Submodule (ZMod p) V)))) =
      Submodule.Quotient.module _ :=
  rfl

example {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] :
    (inferInstance : Module (ZMod p) ↥(Submodule.torsionBy (ZMod p) V (p : ZMod p))) =
      Submodule.module _ :=
  rfl

section Functors

variable {G : Type} [Group G] (p : ℕ) {A B C : Rep.{0} ℤ G}

-- The functors package the object and morphism maps.
example : (modPFunctor p).obj A = repModP p A := rfl

example (f : A ⟶ B) : (modPFunctor p).map f = repModPMap p f := rfl

example : (torsionPFunctor p).obj A = repTorsionP p A := rfl

example (f : A ⟶ B) : (torsionPFunctor p).map f = repTorsionPMap p f := rfl

-- Identity: the map induced by `𝟙 A` fixes every element.
example (x : repModP p A) : ((modPFunctor p).map (𝟙 A)).hom x = x := by simp

example (x : repTorsionP p A) : ((torsionPFunctor p).map (𝟙 A)).hom x = x := by simp

-- Composition: the functors send `f ≫ g` to the composite of the induced maps.
example (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    ((modPFunctor p).map (f ≫ g)).hom (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (g.hom (f.hom a)) := by
  rw [Functor.map_comp, Rep.hom_comp]
  rfl

example (f : A ⟶ B) (g : B ⟶ C) (a : Submodule.torsionBy ℤ A (p : ℤ)) :
    ((((torsionPFunctor p).map (f ≫ g)).hom a : Submodule.torsionBy ℤ C (p : ℤ)) : C) =
      g.hom (f.hom a) := by
  rw [Functor.map_comp, Rep.hom_comp]
  rfl

-- The functors work with the category theory API, e.g. they send isomorphisms to isomorphisms.
example (e : A ≅ B) : repModP p A ≅ repModP p B := (modPFunctor p).mapIso e

example (e : A ≅ B) : repTorsionP p A ≅ repTorsionP p B := (torsionPFunctor p).mapIso e

end Functors

section OptIn

-- An importer that wants the `ZMod p`-module structures as instances opts in to the reducible
-- defs, as for any reducible non-instance; the instance it then finds is the structure the
-- `Rep` objects carry.
attribute [local instance] zmodModuleQuot zmodModuleTorsion

variable {G : Type} [Group G] (p : ℕ) (A : Rep.{0} ℤ G)

example : (inferInstance : Module (ZMod p) ((modPFunctor p).obj A)) =
    ((modPFunctor p).obj A).hV2 :=
  rfl

example : (inferInstance : Module (ZMod p) ((torsionPFunctor p).obj A)) =
    ((torsionPFunctor p).obj A).hV2 :=
  rfl

end OptIn

end Rep
