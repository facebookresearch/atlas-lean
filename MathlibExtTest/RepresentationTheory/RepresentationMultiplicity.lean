/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.RepresentationMultiplicity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace MathlibExtTest.RepresentationTheory.RepresentationMultiplicity

set_option linter.style.haveILetI false

open CharacterTheory

universe u uK uG uV uW

/-- Every one-dimensional representation is irreducible: its subrepresentations
are the submodules of a one-dimensional space, hence only `⊥` and `⊤`. -/
theorem one_dim_rep_irreducible {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] (ρ : Representation k G k) :
    ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine (isSimpleModule_iff _ _).mpr ?_
  have h : Module.finrank k ρ.asModule = 1 := Module.finrank_self k
  exact is_simple_module_of_finrank_eq_one h

/-- Schur, equal case: the intertwining space of the trivial representation
with itself is one-dimensional. -/
example {G : Type} [Group G] [Fintype G] :
    Module.finrank ℂ
      ((Representation.trivial ℂ G ℂ).IntertwiningMap
        (Representation.trivial ℂ G ℂ)) = 1 := by
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible :=
    one_dim_rep_irreducible _
  rw [finrank_intertwiningMap_eq_one_or_zero]
  split_ifs with h
  · rfl
  · exact absurd ⟨Representation.Equiv.refl _⟩ h

/-- The sign representation of `S₃`: a permutation `g` acts on `ℂ` by
multiplication by `sign g`. -/
noncomputable def signRep : Representation ℂ (Equiv.Perm (Fin 3)) ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℂ) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul]
    rw [Equiv.Perm.sign_mul]
    simp only [Units.val_mul, Int.cast_mul]
    ring

/-- The sign representation of `S₃` is not equivalent to the trivial
representation: their characters differ at a transposition (`-1` vs `1`). -/
theorem signRep_not_equiv_trivial :
    ¬Nonempty (Representation.Equiv (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ)
      signRep) := by
  rintro ⟨e⟩
  have hchar := congr_fun (Representation.char_iso e) (Equiv.swap (0 : Fin 3) 1)
  have hsign : signRep.character (Equiv.swap (0 : Fin 3) 1) = -1 := by
    have hfun : ∀ x : ℂ, signRep (Equiv.swap (0 : Fin 3) 1) x = (-1 : ℂ) * x := by
      intro x
      change ((Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) : ℤ) : ℂ) * x = -1 * x
      rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]
      norm_num
    rw [Representation.character,
      show signRep (Equiv.swap (0 : Fin 3) 1) = (-1 : ℂ) • LinearMap.id from
        LinearMap.ext fun x => by
          rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]; exact hfun x,
      LinearMap.map_smul_of_tower, LinearMap.trace_id, smul_eq_mul]
    simp
  have htriv : (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ).character
      (Equiv.swap (0 : Fin 3) 1) = 1 := by
    show LinearMap.trace ℂ ℂ
        ((Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ) (Equiv.swap (0 : Fin 3) 1)) = 1
    rw [show (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ) (Equiv.swap (0 : Fin 3) 1) =
      LinearMap.id from rfl, LinearMap.trace_id]
    simp
  rw [htriv, hsign] at hchar
  norm_num at hchar

/-- Schur, distinct case: the intertwining space between the sign and the
trivial representation of `S₃` is zero-dimensional. -/
example :
    Module.finrank ℂ
      (signRep.IntertwiningMap (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ)) = 0 := by
  haveI : signRep.IsIrreducible := one_dim_rep_irreducible _
  haveI : (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ).IsIrreducible :=
    one_dim_rep_irreducible _
  rw [finrank_intertwiningMap_eq_one_or_zero]
  split_ifs with h
  · exact absurd h signRep_not_equiv_trivial
  · rfl

/-- Multiplicity, two copies: two copies of the trivial representation
decompose as a direct sum with multiplicity `2`, so
`2 = dim Hom_G(trivial, trivial ⊕ trivial)`. -/
example {G : Type} [Group G] [Fintype G] :
    (2 : ℕ) = Module.finrank ℂ
      ((Representation.trivial ℂ G ℂ).IntertwiningMap
        (Representation.directSum (ι := (_i : PUnit) × Fin 2)
          (fun _ : (_i : PUnit) × Fin 2 => Representation.trivial ℂ G ℂ))) := by
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible :=
    one_dim_rep_irreducible _
  have h := multiplicity_eq_finrank_intertwiningMap
    (ρ := fun _ : PUnit => Representation.trivial ℂ G ℂ)
    (σ := Representation.directSum (ι := (_i : PUnit) × Fin 2)
      (fun _ : (_i : PUnit) × Fin 2 => Representation.trivial ℂ G ℂ))
    (d := fun _ : PUnit => 2)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    ⟨Representation.Equiv.refl _⟩
  exact h PUnit.unit

/-- Multiplicity, zero copies: the empty direct sum has multiplicity `0`,
so `0 = dim Hom_G(trivial, 0)`. -/
example {G : Type} [Group G] [Fintype G] :
    (0 : ℕ) = Module.finrank ℂ
      ((Representation.trivial ℂ G ℂ).IntertwiningMap
        (Representation.directSum (ι := (_i : PUnit) × Fin 0)
          (fun _ : (_i : PUnit) × Fin 0 => Representation.trivial ℂ G ℂ))) := by
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible :=
    one_dim_rep_irreducible _
  have h := multiplicity_eq_finrank_intertwiningMap
    (ρ := fun _ : PUnit => Representation.trivial ℂ G ℂ)
    (σ := Representation.directSum (ι := (_i : PUnit) × Fin 0)
      (fun _ : (_i : PUnit) × Fin 0 => Representation.trivial ℂ G ℂ))
    (d := fun _ : PUnit => 0)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    ⟨Representation.Equiv.refl _⟩
  exact h PUnit.unit

open scoped Classical in
/-- Heterogeneous universes: Schur's lemma elaborates with the field, group,
source, and target in four independent universes. This fails to elaborate if
`finrank_intertwiningMap_eq_one_or_zero` fixes `k`, `G`, `V`, and `W` to a
single universe. -/
example {k : Type uK} [Field k] [IsAlgClosed k]
    {G : Type uG} [Group G] [Fintype G]
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type uW} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    Module.finrank k (ρ.IntertwiningMap σ) =
      if Nonempty (Representation.Equiv σ ρ) then 1 else 0 :=
  finrank_intertwiningMap_eq_one_or_zero ρ σ

end MathlibExtTest.RepresentationTheory.RepresentationMultiplicity
