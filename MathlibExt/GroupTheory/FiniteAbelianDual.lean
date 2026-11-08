/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.DirectSum.AddChar
import Mathlib.GroupTheory.FiniteAbelian.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteAbelianDualWanted

open scoped DirectSum

/-!
# Dual groups of finite abelian groups

The dual-group cardinality, basis, and double-dual statements are
`AddChar.card_eq`, `AddChar.complexBasis`, and `AddChar.doubleDualEquiv`; the
(non-canonical) self-duality of a finite abelian group and the product
decomposition of the dual are recorded here.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "dual groups" (reference-only, no Lean formalization);
J.-P. Serre, Linear Representations of Finite Groups, GTM 42 (listed by the
Wanted entry); K. Conrad, Characters of finite abelian groups,
https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Lemma 3.12 and
Theorem 3.13.
-/

private def dual_precomp {α β : Type*} [AddCommGroup α] [AddCommGroup β]
    (e : α ≃+ β) : AddChar β ℂ ≃+ AddChar α ℂ where
  toFun ψ := ψ.compAddMonoidHom e.toAddMonoidHom
  invFun ψ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  left_inv ψ := by
    ext x
    simp
  right_inv ψ := by
    ext x
    simp
  map_add' ψ χ := by
    ext x
    rfl

private def dual_directSumHom {ι : Type*} [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] :
    (∀ i, AddChar (G i) ℂ) →+ AddChar (⨁ i, G i) ℂ := by
  refine
    { toFun := AddChar.directSum
      map_zero' := ?_
      map_add' := ?_ }
  · ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      simp only [AddChar.directSum_apply, DirectSum.toAddMonoid_of]
      rfl
    | add x y hx hy => simp [AddChar.map_add_eq_mul, hx, hy]
  · intro ψ χ
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [AddChar.add_apply]
      simp only [AddChar.directSum_apply, DirectSum.toAddMonoid_of,
        Pi.add_apply, AddChar.toAddMonoidHomEquiv_apply, AddChar.add_apply]
      rfl
    | add x y hx hy =>
      simp only [AddChar.map_add_eq_mul, AddChar.add_apply, hx, hy]

private noncomputable def dual_zmodFamilyHom {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    (⨁ i, ZMod (n i)) →+ (∀ i, AddChar (ZMod (n i)) ℂ) where
  toFun u i := AddChar.zmodAddEquiv (u i)
  map_zero' := by
    funext i
    exact map_zero AddChar.zmodAddEquiv
  map_add' u v := by
    funext i
    exact map_add AddChar.zmodAddEquiv (u i) (v i)

private noncomputable def dual_zmodDirectSumHom {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    (⨁ i, ZMod (n i)) →+ AddChar (⨁ i, ZMod (n i)) ℂ :=
  dual_directSumHom.comp (dual_zmodFamilyHom n)

private theorem dual_zmodFamilyHom_injective {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    Function.Injective (dual_zmodFamilyHom n) := by
  intro u v h
  ext i
  apply AddChar.zmodAddEquiv.injective
  exact congrFun h i

private theorem dual_zmodDirectSumHom_injective {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    Function.Injective (dual_zmodDirectSumHom n) :=
  AddChar.directSum_injective.comp (dual_zmodFamilyHom_injective n)

private noncomputable def dual_zmodDirectSumEquiv {ι : Type*} [Fintype ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    (⨁ i, ZMod (n i)) ≃+ AddChar (⨁ i, ZMod (n i)) ℂ := by
  classical
  letI : Fintype (⨁ i, ZMod (n i)) :=
    Fintype.ofEquiv (∀ i, ZMod (n i)) (DirectSum.addEquivProd _).symm.toEquiv
  refine AddEquiv.ofBijective (dual_zmodDirectSumHom n) ?_
  rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
  exact ⟨dual_zmodDirectSumHom_injective n, rfl⟩

private def dual_prodEquiv (α β : Type*) [AddCommGroup α] [AddCommGroup β] :
    AddChar (α × β) ℂ ≃+ (AddChar α ℂ × AddChar β ℂ) where
  toFun ψ :=
    (ψ.compAddMonoidHom (AddMonoidHom.inl α β),
      ψ.compAddMonoidHom (AddMonoidHom.inr α β))
  invFun χ :=
    { toFun := fun x => χ.1 x.1 * χ.2 x.2
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
        ac_rfl }
  left_inv ψ := by
    ext x
    rcases x with ⟨x, y⟩
    change ψ (x, 0) * ψ (0, y) = ψ (x, y)
    rw [← AddChar.map_add_eq_mul]
    simp
  right_inv χ := by
    ext x <;> simp
  map_add' ψ χ := by
    ext x <;> rfl

/--
A finite abelian group is (non-canonically) isomorphic to its dual group.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "dual groups"; K. Conrad, Characters of finite abelian groups,
https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Theorem 3.13.

Proves `Wanted` entry `finite_abelian_dual_iso`.

Proof: Use the finite abelian structure theorem, apply `AddChar.zmodAddEquiv`
coordinatewise on the cyclic factors, and transport characters along the
decomposition. This is the proof of Conrad's Theorem 3.13: the cyclic case,
then products of cyclic groups.
-/
public theorem finite_abelian_dual_iso (α : Type*) [AddCommGroup α]
    [Finite α] : Nonempty (α ≃+ AddChar α ℂ) := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  have hn' : ∀ i, NeZero (n i) := fun i => by
    have := hn i
    exact ⟨by positivity⟩
  exact ⟨e.trans <| (@dual_zmodDirectSumEquiv ι inferInstance n hn').trans <|
    dual_precomp e⟩

/--
The dual of a product is the product of the duals.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "dual groups"; K. Conrad, Characters of finite abelian groups,
https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Lemma 3.12.

Proves `Wanted` entry `dual_prod`.

Proof: Restrict a character along the two coordinate inclusions, with inverse
`(χ₁, χ₂) ↦ fun (x, y) ↦ χ₁ x * χ₂ y`. Conrad's Lemma 3.12 uses the same
restriction map for finite groups and concludes by counting; the explicit
inverse removes the finiteness assumption.
-/
public theorem dual_prod (α β : Type*) [AddCommGroup α] [AddCommGroup β] :
    Nonempty (AddChar (α × β) ℂ ≃+ (AddChar α ℂ × AddChar β ℂ)) := by
  exact ⟨dual_prodEquiv α β⟩

end MathlibExt.GroupTheory.FiniteAbelianDualWanted
