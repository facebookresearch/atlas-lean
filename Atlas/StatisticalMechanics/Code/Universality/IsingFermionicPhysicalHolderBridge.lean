/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalDeepEnergy











namespace StatMech.Universality

open Finset

noncomputable section



noncomputable def fkIsingSquareRadialPatchDeepVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) : Real :=
  (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
      |fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) base d.snd -
        fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) base d.fst|) +
    ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
      |fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base d.snd -
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base d.fst|

theorem fkIsingSquareRadialPatchDeepVariation_nonneg
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) :
    0 ≤ fkIsingSquareRadialPatchDeepVariation n m hn hm hm2 r base := by
  unfold fkIsingSquareRadialPatchDeepVariation
  positivity


noncomputable def fkIsingSquareRadialPatchPhysicalNormalizedWindow
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogBox R → Complex :=
  fun p ↦ fkIsingSquareRadialPatchFullObservableWindow
      n m baseI baseJ R hn hm hfitI hfitJ p /
    (Real.sqrt (2 * mesh) : Complex)





theorem fkIsingSquareRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
    (n m baseI baseJ R rho : Nat) (mesh d H V : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat) (base : Real)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareRadialPatchDeepVariation
      n m hn hm hm2 r base ≤ V)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hradius : d ≤ mesh * (rho : Real))
    (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow
          n m baseI baseJ R mesh hn hm hfitI hfitJ p -
        fkIsingSquareRadialPatchPhysicalNormalizedWindow
          n m baseI baseJ R mesh hn hm hfitI hfitJ p'‖ ≤ mesh * H := by
  let F := fkIsingSquareRadialPatchPhysicalNormalizedWindow
    n m baseI baseJ R mesh hn hm hfitI hfitJ
  have hdiff : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * mesh *
        fkIsingSquareRadialPatchDeepVariation n m hn hm hm2 r base := by
    simpa [F, fkIsingSquareRadialPatchPhysicalNormalizedWindow,
      fkIsingSquareRadialPatchDeepVariation] using
      fkIsingSquareRadialPatchFullObservableWindow_deep_diffusive
        n m baseI baseJ R rho mesh hn hm hm2 hfitI hfitJ hmesh r base
        hdeep p p' hrho hp hp' hpp'
  have hfactor : 0 ≤ (1032080 / (rho : Real) ^ 3) * mesh := by positivity
  have hdiffV : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * mesh * V :=
    hdiff.trans (mul_le_mul_of_nonneg_left hV hfactor)
  have hrhoReal : 0 < (rho : Real) := by positivity
  have hradiusPow : d ^ 3 ≤ (mesh * (rho : Real)) ^ 3 :=
    pow_le_pow_left₀ hd hradius 3
  have hscale' : 1032080 * V ≤
      H ^ 2 * (mesh * (rho : Real)) ^ 3 :=
    hscale.trans (mul_le_mul_of_nonneg_left hradiusPow (sq_nonneg H))
  have hdiv : 1032080 * V / (rho : Real) ^ 3 ≤ H ^ 2 * mesh ^ 3 := by
    apply (div_le_iff₀ (pow_pos hrhoReal 3)).2
    calc
      1032080 * V ≤ H ^ 2 * (mesh * (rho : Real)) ^ 3 := hscale'
      _ = (H ^ 2 * mesh ^ 3) * (rho : Real) ^ 3 := by ring
  have hrhs : (1032080 / (rho : Real) ^ 3) * mesh * V ≤
      mesh ^ 4 * H ^ 2 := by
    calc
      (1032080 / (rho : Real) ^ 3) * mesh * V =
          mesh * (1032080 * V / (rho : Real) ^ 3) := by ring
      _ ≤ mesh * (H ^ 2 * mesh ^ 3) :=
        mul_le_mul_of_nonneg_left hdiv hmesh.le
      _ = mesh ^ 4 * H ^ 2 := by ring
  have hfinal : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      mesh ^ 4 * H ^ 2 := hdiffV.trans hrhs
  have hmult : mesh ^ 2 * ‖F p - F p'‖ ^ 2 ≤
      mesh ^ 2 * (mesh * H) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hfinal.trans_eq (by ring)
  have hsquare : ‖F p - F p'‖ ^ 2 ≤ (mesh * H) ^ 2 :=
    le_of_mul_le_mul_left hmult (pow_pos hmesh 2)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hmesh.le hH)).mp hsquare





theorem fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path
    (n m baseI baseJ R rho steps : Nat) (mesh d H V B D : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat) (base : Real)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareRadialPatchDeepVariation
      n m hn hm hm2 r base ≤ V)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hradius : d ≤ mesh * (rho : Real))
    (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
    (hrho : 0 < rho)
    (gamma : Nat → IsingLeapfrogBox R)
    (hmargin : ∀ k ≤ steps, IsingLeapfrogInteriorMargin R rho (gamma k))
    (hadjacent : ∀ k < steps,
      IsingLeapfrogDiagonalAdjacent (gamma k) (gamma (k + 1)))
    (hstart : ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow
      n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma 0)‖ ≤ B)
    (hlength : mesh * (steps : Real) ≤ D) :
    ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow
      n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma steps)‖ ≤
        B + D * H := by
  let F := fkIsingSquareRadialPatchPhysicalNormalizedWindow
    n m baseI baseJ R mesh hn hm hfitI hfitJ
  have hstep (k : Nat) (hk : k < steps) :
      ‖F (gamma (k + 1)) - F (gamma k)‖ ≤ mesh * H := by
    rw [norm_sub_rev]
    exact
      fkIsingSquareRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
        n m baseI baseJ R rho mesh d H V hn hm hm2 hfitI hfitJ hmesh
        r base hdeep hV hd hH hradius hscale (gamma k) (gamma (k + 1))
        hrho (hmargin k (by omega)) (hmargin (k + 1) (by omega))
        (hadjacent k hk)
  have hpath (k : Nat) (hk : k ≤ steps) :
      ‖F (gamma k)‖ ≤ ‖F (gamma 0)‖ + (k : Real) * (mesh * H) := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          ‖F (gamma (k + 1))‖ ≤
              ‖F (gamma k)‖ + ‖F (gamma (k + 1)) - F (gamma k)‖ :=
            norm_le_norm_add_norm_sub' _ _
          _ ≤ (‖F (gamma 0)‖ + (k : Real) * (mesh * H)) + mesh * H :=
            add_le_add (ih (by omega)) (hstep k (by omega))
          _ = ‖F (gamma 0)‖ + ((k + 1 : Nat) : Real) * (mesh * H) := by
            push_cast
            ring
  calc
    ‖F (gamma steps)‖ ≤ ‖F (gamma 0)‖ + (steps : Real) * (mesh * H) :=
      hpath steps (le_refl steps)
    _ ≤ B + (steps : Real) * (mesh * H) :=
      add_le_add hstart (le_refl _)
    _ = B + (mesh * (steps : Real)) * H := by ring
    _ ≤ B + D * H := add_le_add (le_refl B)
      (mul_le_mul_of_nonneg_right hlength hH)




theorem fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path_explicit
    (n m baseI baseJ R rho steps : Nat) (mesh d V B D : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat) (base : Real)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareRadialPatchDeepVariation
      n m hn hm hm2 r base ≤ V)
    (hd : 0 < d) (hradius : d ≤ mesh * (rho : Real)) (hrho : 0 < rho)
    (gamma : Nat → IsingLeapfrogBox R)
    (hmargin : ∀ k ≤ steps, IsingLeapfrogInteriorMargin R rho (gamma k))
    (hadjacent : ∀ k < steps,
      IsingLeapfrogDiagonalAdjacent (gamma k) (gamma (k + 1)))
    (hstart : ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow
      n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma 0)‖ ≤ B)
    (hlength : mesh * (steps : Real) ≤ D) :
    ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow
      n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma steps)‖ ≤
        B + D * Real.sqrt (1032080 * V / d ^ 3) := by
  have hVnonneg : 0 ≤ V :=
    (fkIsingSquareRadialPatchDeepVariation_nonneg
      n m hn hm hm2 r base).trans hV
  let H := Real.sqrt (1032080 * V / d ^ 3)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hscale : 1032080 * V ≤ H ^ 2 * d ^ 3 := by
    have harg : 0 ≤ 1032080 * V / d ^ 3 := by positivity
    dsimp [H]
    rw [Real.sq_sqrt harg]
    field_simp [ne_of_gt hd]
    exact le_rfl
  simpa [H] using
    fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path
      n m baseI baseJ R rho steps mesh d H V B D hn hm hm2 hfitI hfitJ
      hmesh r base hdeep hV hd.le hH hradius hscale hrho gamma hmargin
      hadjacent hstart hlength

end

end StatMech.Universality
