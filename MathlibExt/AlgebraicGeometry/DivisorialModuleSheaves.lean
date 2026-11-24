/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import MathlibExt.AlgebraicGeometry.RationalFunctionModules
public import MathlibExt.AlgebraicGeometry.LogPairs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# The sheaf `𝒪_X(D)` of a Weil divisor

For an integral Weil divisor `D` on a normal variety `X` whose codimension-one local rings are
discrete valuation rings, `𝒪_X(D)` is the subsheaf of the sheaf `𝒦_X` of rational functions with
`Γ(U, 𝒪_X(D)) = {f ∈ K(X) | f = 0 or ord_p f ≥ -D(p) for every prime divisor p ∈ U}`.

`sections`, `mem_sections`, `sections_map`, `submodule`, `sheaf` and `inclusion` are ported from
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean` in TauCetiProject/TauCeti at revision
62bbc0596dc3539d488232e4e924a338548ea0a9 (Apache 2.0), with Weil divisors replaced by
`LogPairs.IntegerWeil` on the prime points of a `LogPairs.NormalVariety`. The inclusion `ofLE`
for coefficientwise comparable divisors is new.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.AlgebraicGeometry _root_.Opposite
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RationalFunctionModules

variable {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n)
  [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]

/-- Actual O(D) sections, with the coefficient inequality imposed at every prime point. -/
def sections (D : IntegerWeil V) (U : V.X.left.Opens) :
    Submodule Γ(V.X.left, U) Γ(rationalFunctions V.X.left, U) where
  carrier := {s | ∀ (p : PrimePoint V) (hp : p.val ∈ U),
    haveI : Nonempty U := ⟨⟨p.val, hp⟩⟩
    rationalFunctionsEquiv U s = 0 ∨
      -D p ≤ V.X.left.ord (rationalFunctionsEquiv U s) p.val}
  zero_mem' := by
    intro p hp
    have : Nonempty U := ⟨⟨p.val, hp⟩⟩
    exact Or.inl (map_zero _)
  add_mem' := by
    intro s t hs ht p hp
    have : Nonempty U := ⟨⟨p.val, hp⟩⟩
    rw [map_add]
    rcases hs p hp with h₁ | h₁
    · rw [h₁, zero_add]
      exact ht p hp
    · rcases ht p hp with h₂ | h₂
      · rw [h₂, add_zero]
        exact Or.inr h₁
      · by_cases h : rationalFunctionsEquiv U s + rationalFunctionsEquiv U t = 0
        · exact Or.inl h
        · exact Or.inr <| le_trans (le_min h₁ h₂) (Scheme.ord_add h)
  smul_mem' := by
    intro r s hs p hp
    have : Nonempty U := ⟨⟨p.val, hp⟩⟩
    rw [map_smul]
    rcases eq_or_ne r 0 with rfl | hr
    · exact Or.inl (by simp)
    · rcases hs p hp with h₁ | h₁
      · exact Or.inl (by rw [h₁, smul_zero])
      · exact Or.inr <| h₁.trans (Scheme.ord_le_smul hp hr _)

@[simp]
theorem mem_sections {D : IntegerWeil V} {U : V.X.left.Opens}
    {s : Γ(rationalFunctions V.X.left, U)} :
    s ∈ sections V D U ↔ ∀ (p : PrimePoint V) (hp : p.val ∈ U),
      haveI : Nonempty U := ⟨⟨p.val, hp⟩⟩
      rationalFunctionsEquiv U s = 0 ∨
        -D p ≤ V.X.left.ord (rationalFunctionsEquiv U s) p.val := Iff.rfl

theorem sections_map {D : IntegerWeil V} {U W : V.X.left.Opens} (i : W ⟶ U)
    {s : Γ(rationalFunctions V.X.left, U)} (hs : s ∈ sections V D U) :
    (rationalFunctions V.X.left).presheaf.map i.op s ∈ sections V D W := by
  refine (mem_sections V).mpr fun p hp ↦ ?_
  have : Nonempty W := ⟨⟨p.val, hp⟩⟩
  have : Nonempty U := ⟨⟨p.val, i.le hp⟩⟩
  rw [rationalFunctionsEquiv_map]
  exact (mem_sections V).mp hs p (i.le hp)

/-- The order condition is local, giving an actual subsheaf of K_X. -/
def submodule (D : IntegerWeil V) : (rationalFunctions V.X.left).Submodule where
  obj U := sections V D U.unop
  map i := fun {_} hs ↦ sections_map V i.unop hs
  isSheaf {U} s hs := by
    refine (mem_sections V).mpr fun p hp ↦ ?_
    obtain ⟨W, i, hi, hpW⟩ := hs p.val hp
    have : Nonempty W := ⟨⟨p.val, hpW⟩⟩
    have : Nonempty U.unop := ⟨⟨p.val, hp⟩⟩
    have h := (mem_sections V).mp hi p hpW
    rw [← rationalFunctionsEquiv_map i s]
    exact h

/-- The completed actual divisorial sheaf O_X(D). -/
def sheaf (D : IntegerWeil V) : V.X.left.Modules :=
  (submodule V D).toSheafOfModules

/-- Its actual inclusion into the rational-function module. -/
def inclusion (D : IntegerWeil V) : sheaf V D ⟶ rationalFunctions V.X.left :=
  (submodule V D).ι

/-- Coefficientwise divisor containment induces the literal subtype inclusion. -/
def ofLE {D E : IntegerWeil V} (h : ∀ p, D p ≤ E p) : sheaf V D ⟶ sheaf V E where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun s ↦
            ⟨s.val, by
              intro p hp
              rcases s.property p hp with hz | ho
              · exact Or.inl hz
              · exact Or.inr ((neg_le_neg (h p)).trans ho)⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality := by
        intro U W f
        ext s
        rfl }

/-- `ofLE` is compatible with the inclusions into the rational-function module. -/
@[reassoc (attr := simp)]
theorem ofLE_inclusion {D E : IntegerWeil V} (h : ∀ p, D p ≤ E p) :
    ofLE V h ≫ inclusion V E = inclusion V D :=
  rfl

end MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
