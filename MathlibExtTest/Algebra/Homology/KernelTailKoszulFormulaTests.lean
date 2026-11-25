/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.ChainComplexKernelTail
import MathlibExt.Algebra.Homology.KoszulComplexFamily

/-!
# Kernel-tail augmentation and low-degree Koszul formulas

The tail augmentation factors the original differential through the kernel
of its augmentation. Its degree-zero component followed by the kernel
inclusion is the original differential. The two-generator Koszul formula
has one positive and one negative term, in the order of the generators.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace MathlibExtTest.Algebra.Homology

section KernelTail

variable {C : Type u} [Category.{v} C] [Abelian C]
  (Q : ChainComplex C ℕ) (X : C) (π : Q ⟶ (ChainComplex.single₀ C).obj X)

/-- The tail augmentation has the original first differential under the kernel inclusion. -/
example : (ChainComplex.kernelTailAugmentation π).f 0 ≫ kernel.ι (π.f 0) = Q.d 1 0 := by
  rw [ChainComplex.kernelTailAugmentation_f_zero]
  exact kernel.lift_ι _ _ _

/-- The two original low-degree quasi-isomorphisms suffice for the tail's degree zero. -/
example [QuasiIsoAt π 0] [QuasiIsoAt π 1] :
    QuasiIsoAt (ChainComplex.kernelTailAugmentation π) 0 :=
  ChainComplex.quasiIsoAt_zero_kernelTailAugmentation π

end KernelTail

section Koszul

variable (R : Type u) [CommRing R]

/-- The ordered two-generator wedge has differential `a₀ e₁ - a₁ e₀`. -/
example (a : Fin 2 → R) :
    KoszulComplex.differential R (Fin 2 → R) (KoszulComplex.familyFunctional R a) 1
        (exteriorPower.ιMulti R 2 (fun i => (Pi.single i 1 : Fin 2 → R))) =
      a 0 • exteriorPower.ιMulti R 1 (fun _ => (Pi.single (1 : Fin 2) 1 : Fin 2 → R)) -
        a 1 • exteriorPower.ιMulti R 1 (fun _ => (Pi.single (0 : Fin 2) 1 : Fin 2 → R)) := by
  have hsucc : (fun q : Fin 1 => (Pi.single q.succ 1 : Fin 2 → R)) =
      (fun _ : Fin 1 => (Pi.single (1 : Fin 2) 1 : Fin 2 → R)) := by
    funext q
    have hq : q = 0 := Subsingleton.elim _ _
    subst q
    rfl
  have hdelete : (fun q : Fin 1 => (Pi.single (Fin.succAbove (1 : Fin 2) q) 1 : Fin 2 → R)) =
      (fun _ : Fin 1 => (Pi.single (0 : Fin 2) 1 : Fin 2 → R)) := by
    funext q
    have hq : q = 0 := Subsingleton.elim _ _
    subst q
    rfl
  rw [KoszulComplex.familyDifferential_apply_basis]
  simp [Fin.sum_univ_two, sub_eq_add_neg, hsucc, hdelete]
  exact neg_smul (a 1)
    (exteriorPower.ιMulti R 1 (fun _ => (Pi.single (0 : Fin 2) 1 : Fin 2 → R)))

/-- The empty family generates the zero ideal. -/
example (a : Fin 0 → R) :
    KoszulComplex.ideal R (Fin 0 → R) (KoszulComplex.familyFunctional R a) = ⊥ := by
  rw [KoszulComplex.familyIdeal_eq_span]
  simp

end Koszul

end MathlibExtTest.Algebra.Homology
