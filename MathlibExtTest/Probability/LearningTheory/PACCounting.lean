/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.PACCounting

@[expose] public section

/-- A hypothesis equal to the target is consistent on all samples. -/
example : (Finset.univ.filter (fun s : Fin 2 → Fin 3 =>
      ∀ i, (fun _ : Fin 3 => true) (s i) = (fun _ : Fin 3 => true) (s i))).card
    = (Finset.univ.filter (fun x : Fin 3 =>
        (fun _ : Fin 3 => true) x = (fun _ : Fin 3 => true) x)).card ^ 2 :=
  card_consistent (fun _ : Fin 3 => true) (fun _ : Fin 3 => true) 2

end
