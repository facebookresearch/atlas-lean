/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.UnramifiedMonogenic

/-!
# Tests for unramified DVR extensions are monogenic with separable reduced
# minimal polynomial

These examples exercise the two public theorems of
`MathlibExt.RingTheory.DiscreteValuationRing.UnramifiedMonogenic`:
the Corollary 10.15 equivalence in both directions, the identity extension
end to end, and the Corollary 10.16 cyclotomic criterion.
-/

@[expose] public section

open IsLocalRing IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
  [Module.IsTorsionFree A B] [IsAdicComplete (maximalIdeal A) A]

/-- The forward direction of the Corollary 10.15 equivalence applies
as stated. -/
example (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B))
    (hdeg : Module.finrank A B =
      Module.finrank (ResidueField A) (ResidueField B)) :
    ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ ∧
      ((minpoly A α).map (residue A)).Separable :=
  unramified_iff_exists_monogenic_separable_reduced_minpoly.mp ⟨hsep, hdeg⟩

/-- The reverse direction of the Corollary 10.15 equivalence applies
as stated. -/
example (α : B) (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
    (hsep : ((minpoly A α).map (residue A)).Separable) :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) ∧
      Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B) :=
  unramified_iff_exists_monogenic_separable_reduced_minpoly.mpr ⟨α, hα, hsep⟩

/-- End-to-end check on the identity extension: it is unramified, so the
forward direction produces a generator with separable reduced minimal
polynomial. -/
example (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] :
    ∃ α : A, Algebra.adjoin A ({α} : Set A) = ⊤ ∧
      ((minpoly A α).map (residue A)).Separable := by
  let _ : Algebra A A := Algebra.id A
  have hfin : Module.finrank A A =
      Module.finrank (ResidueField A) (ResidueField A) := by
    rw [Module.finrank_self, Module.finrank_self]
  exact unramified_iff_exists_monogenic_separable_reduced_minpoly.mp
    ⟨inferInstance, hfin⟩

/-- Generic application of the Corollary 10.16 cyclotomic criterion. -/
example {n : ℕ} {ζ : B} (hprim : IsPrimitiveRoot ζ n)
    (hcoprime : Nat.Coprime n (ringChar (IsLocalRing.ResidueField A)))
    (hgen : Algebra.adjoin A ({ζ} : Set B) = ⊤) :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) ∧
      Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B) :=
  unramified_of_primitive_root_of_unity_of_coprime hprim hcoprime hgen
