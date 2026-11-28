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

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Homotopy components descending through a cokernel

Let a : Y → X be a map of nonnegative chain complexes of modules over a ring R. Suppose
homotopies H on X and H′ on Y satisfy a_n ≫ H(n,m) = H′(n,m) ≫ a_m for every n,m. Their
components then descend through the degreewise cokernels to maps on coker(a).

For supplied endomorphisms F,G of coker(a) satisfying πa ≫ F = f ≫ πa and πa ≫ G = g ≫ πa,
these constructed components form a homotopy F ≃ G. The ring and module carrier universes are
independent.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Homotopy

section CokernelDescent

variable {R : Type u} [Ring R]

/-- The homotopy component induced on a cokernel.

Using the compatible homotopy components H and H′, descend H(n,m) followed by the target
cokernel projection to a map (coker a)_n → (coker a)_m. -/
noncomputable def cokernelDescHomotopyHom {KX KY : ChainComplex (ModuleCat.{v} R) ℕ}
    (a : KY ⟶ KX) {f g : KX ⟶ KX} {f' g' : KY ⟶ KY}
    (H : Homotopy f g) (H' : Homotopy f' g')
    (hcompat : ∀ n m, a.f n ≫ H.hom n m = H'.hom n m ≫ a.f m)
    (n m : ℕ) : (cokernel a).X n ⟶ (cokernel a).X m :=
  (PreservesCokernel.iso (HomologicalComplex.eval _ _ n) a).hom ≫
    cokernel.desc ((HomologicalComplex.eval _ _ n).map a)
      (H.hom n m ≫ (cokernel.π a).f m)
      (by
        have hkill : a.f m ≫ (cokernel.π a).f m = 0 := by
          have e := congrArg (fun t => t.f m) (cokernel.condition a)
          rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at e
          exact e
        change (HomologicalComplex.eval _ _ n).map a ≫
          (H.hom n m ≫ (cokernel.π a).f m) = 0
        rw [HomologicalComplex.eval_map, ← Category.assoc, hcompat n m,
          Category.assoc, hkill, comp_zero])

/-- The descended component commutes with the cokernel projection.

The projection in degree n followed by the descended component equals H(n,m) followed by the
projection in degree m. -/
theorem cokernelDescHomotopyHom_compat {KX KY : ChainComplex (ModuleCat.{v} R) ℕ}
    (a : KY ⟶ KX) {f g : KX ⟶ KX} {f' g' : KY ⟶ KY}
    (H : Homotopy f g) (H' : Homotopy f' g')
    (hcompat : ∀ n m, a.f n ≫ H.hom n m = H'.hom n m ≫ a.f m)
    (n m : ℕ) :
    (cokernel.π a).f n ≫ cokernelDescHomotopyHom a H H' hcompat n m =
    H.hom n m ≫ (cokernel.π a).f m := by
  change (HomologicalComplex.eval _ _ n).map (cokernel.π a) ≫
    cokernelDescHomotopyHom a H H' hcompat n m = _
  unfold cokernelDescHomotopyHom
  rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

/-- The homotopy on supplied descended endomorphisms.

For F,G on coker(a) obeying the endpoint projection squares and compatible H,H′, the
components descended through the cokernel form a homotopy from F to G. -/
noncomputable def cokernelDescHomotopy {KX KY : ChainComplex (ModuleCat.{v} R) ℕ}
    (a : KY ⟶ KX) {f g : KX ⟶ KX} {f' g' : KY ⟶ KY}
    (F G : cokernel a ⟶ cokernel a)
    (hF : cokernel.π a ≫ F = f ≫ cokernel.π a)
    (hG : cokernel.π a ≫ G = g ≫ cokernel.π a)
    (H : Homotopy f g) (H' : Homotopy f' g')
    (hcompat : ∀ n m, a.f n ≫ H.hom n m = H'.hom n m ≫ a.f m) :
    Homotopy F G where
  hom := cokernelDescHomotopyHom a H H' hcompat
  zero n m hnm := by
    have h0 : H.hom n m = 0 := H.zero n m hnm
    have key : (cokernel.π a).f n ≫ cokernelDescHomotopyHom a H H' hcompat n m = 0 := by
      rw [cokernelDescHomotopyHom_compat, h0, zero_comp]
    have e2 : (cokernel.π a).f n ≫
        (0 : (cokernel a).X n ⟶ (cokernel a).X m) = 0 := comp_zero
    exact (cancel_epi ((cokernel.π a).f n)).mp (key.trans e2.symm)
  comm i := by
    have hFf : (cokernel.π a).f i ≫ F.f i =
        f.f i ≫ (cokernel.π a).f i := by
      have e := congrArg (fun t => t.f i) hF
      simpa [HomologicalComplex.comp_f] using e
    have hGf : (cokernel.π a).f i ≫ G.f i =
        g.f i ≫ (cokernel.π a).f i := by
      have e := congrArg (fun t => t.f i) hG
      simpa [HomologicalComplex.comp_f] using e
    have hhom : ∀ n m, (cokernel.π a).f n ≫
        cokernelDescHomotopyHom a H H' hcompat n m =
        H.hom n m ≫ (cokernel.π a).f m :=
      fun n m => cokernelDescHomotopyHom_compat a H H' hcompat n m
    have hd : (cokernel.π a).f i ≫
        dNext i (cokernelDescHomotopyHom a H H' hcompat) =
        dNext i H.hom ≫ (cokernel.π a).f i := by
      cases i with
      | zero =>
          rw [Homotopy.dNext_zero_chainComplex,
            Homotopy.dNext_zero_chainComplex, comp_zero, zero_comp]
      | succ i =>
          rw [Homotopy.dNext_succ_chainComplex,
            Homotopy.dNext_succ_chainComplex]
          have hcommd : (cokernel.π a).f (i + 1) ≫
              (cokernel a).d (i + 1) i =
              KX.d (i + 1) i ≫ (cokernel.π a).f i :=
            HomologicalComplex.Hom.comm _ _ _
          calc (cokernel.π a).f (i + 1) ≫
                  ((cokernel a).d (i + 1) i ≫
                    cokernelDescHomotopyHom a H H' hcompat i (i + 1))
              = ((cokernel.π a).f (i + 1) ≫
                  (cokernel a).d (i + 1) i) ≫
                cokernelDescHomotopyHom a H H' hcompat i (i + 1) :=
                (Category.assoc _ _ _).symm
            _ = (KX.d (i + 1) i ≫ (cokernel.π a).f i) ≫
                cokernelDescHomotopyHom a H H' hcompat i (i + 1) :=
                congrArg (· ≫ _) hcommd
            _ = KX.d (i + 1) i ≫
                ((cokernel.π a).f i ≫
                  cokernelDescHomotopyHom a H H' hcompat i (i + 1)) :=
                Category.assoc _ _ _
            _ = KX.d (i + 1) i ≫
                (H.hom i (i + 1) ≫ (cokernel.π a).f (i + 1)) :=
                congrArg _ (hhom i (i + 1))
            _ = (KX.d (i + 1) i ≫ H.hom i (i + 1)) ≫
                (cokernel.π a).f (i + 1) :=
                (Category.assoc _ _ _).symm
    have hp : (cokernel.π a).f i ≫
        prevD i (cokernelDescHomotopyHom a H H' hcompat) =
        prevD i H.hom ≫ (cokernel.π a).f i := by
      rw [Homotopy.prevD_chainComplex, Homotopy.prevD_chainComplex]
      have hcommd : (cokernel.π a).f (i + 1) ≫
          (cokernel a).d (i + 1) i =
          KX.d (i + 1) i ≫ (cokernel.π a).f i :=
        HomologicalComplex.Hom.comm _ _ _
      calc (cokernel.π a).f i ≫
              (cokernelDescHomotopyHom a H H' hcompat i (i + 1) ≫
                (cokernel a).d (i + 1) i)
          = ((cokernel.π a).f i ≫
              cokernelDescHomotopyHom a H H' hcompat i (i + 1)) ≫
            (cokernel a).d (i + 1) i :=
            (Category.assoc _ _ _).symm
        _ = (H.hom i (i + 1) ≫ (cokernel.π a).f (i + 1)) ≫
            (cokernel a).d (i + 1) i :=
            congrArg (· ≫ _) (hhom i (i + 1))
        _ = H.hom i (i + 1) ≫
            ((cokernel.π a).f (i + 1) ≫ (cokernel a).d (i + 1) i) :=
            Category.assoc _ _ _
        _ = H.hom i (i + 1) ≫
            (KX.d (i + 1) i ≫ (cokernel.π a).f i) :=
            congrArg _ hcommd
        _ = (H.hom i (i + 1) ≫ KX.d (i + 1) i) ≫
            (cokernel.π a).f i :=
            (Category.assoc _ _ _).symm
    refine (cancel_epi ((cokernel.π a).f i)).mp ?_
    rw [Preadditive.comp_add, Preadditive.comp_add, hFf, hGf, hd, hp,
      ← Preadditive.add_comp, ← Preadditive.add_comp, H.comm i]

end CokernelDescent

end Homotopy

end
