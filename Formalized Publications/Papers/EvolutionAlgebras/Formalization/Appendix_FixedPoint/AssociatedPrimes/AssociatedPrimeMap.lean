/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Associated prime yields a nonzero map out of the quotient (GapBase D6)

For `P ∈ Ass(M)` over a Noetherian commutative ring, the quotient `R ⧸ P`
embeds into `M`, hence admits a nonzero map to `M`. Stated as three rungs —
linear core, `ModuleCat` rung, `Ext⁰` rung — so the 17.2 consumer (UnmixedSqueeze)
takes whichever form its squeeze needs without re-proving the embedding.
The `∃ e, e ≠ 0` (not `Nontrivial`) form contradicts IschebeckAssembly's
`Subsingleton (Ext N M 0)` vanishing by one `Subsingleton.elim`.

`[IsAlgClosed]`: not required and not used — everything here is over a
general commutative Noetherian ring with no field hypotheses.
-/

universe v u

open CategoryTheory Abelian

variable {R : Type v} [CommRing R] [IsNoetherianRing R] [Small.{v} R]

omit [Small.{v} R] in
/-- D6 core (linear): an associated prime yields a nonzero map out of
    the quotient. No `Small` content; universe-clean. -/
theorem assHom_ne_zero {M : Type v} [AddCommGroup M] [Module R M]
    {P : Ideal R} (hP : IsAssociatedPrime P M) :
    ∃ f : R ⧸ P →ₗ[R] M, f ≠ 0 := by
  obtain ⟨hprime, f, hf⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap P M).mp hP
  refine ⟨f, ?_⟩
  intro h0
  subst h0
  have hnt : Nontrivial (R ⧸ P) :=
    Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
  have hsub : Subsingleton (R ⧸ P) := ⟨fun x y ↦ hf (by simp)⟩
  exact not_nontrivial_iff_subsingleton.mpr hsub hnt

omit [Small.{v} R] in
/-- D6 ModuleCat rung: the same map as a nonzero morphism. -/
theorem assHom_cat_ne_zero {M : ModuleCat.{v} R}
    {P : Ideal R} (hP : IsAssociatedPrime P (M : Type v)) :
    ∃ g : ModuleCat.of R (R ⧸ P) ⟶ M, g ≠ 0 := by
  obtain ⟨f, hf⟩ := assHom_ne_zero hP
  refine ⟨ModuleCat.ofHom f, ?_⟩
  intro h0
  apply hf
  have h1 := congrArg ModuleCat.Hom.hom h0
  simpa using h1

omit [Small.{v} R] in
/-- D6 Ext⁰ rung (17.2 input for UnmixedSqueeze): `Ext⁰` is nontrivial. -/
theorem assExt_zero_ne [HasExt.{v} (ModuleCat.{v} R)]
    {M : ModuleCat.{v} R}
    {P : Ideal R} (hP : IsAssociatedPrime P (M : Type v)) :
    ∃ e : Ext (ModuleCat.of R (R ⧸ P)) M 0, e ≠ 0 := by
  obtain ⟨g, hg⟩ := assHom_cat_ne_zero hP
  refine ⟨Ext.mk₀ g, ?_⟩
  intro h0
  apply hg
  exact (Ext.mk₀_bijective _ _).injective (by simp [h0])
