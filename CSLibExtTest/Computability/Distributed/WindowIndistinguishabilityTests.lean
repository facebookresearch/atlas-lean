/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.WindowIndistinguishability

/-!
# Tests for window indistinguishability

* The algorithm that colors each vertex by its own identifier properly colors every directed
  cycle, so the hypothesis of `window_colors_differ` is satisfiable, and the theorem applies to
  the windows `(0, 1, 2)` and `(1, 2, 3)`.
-/

@[expose] public section

namespace Cslib.Distributed.WindowIndistinguishabilityTests

open Cslib.Distributed.WindowIndistinguishability

/-- Coloring by one's own identifier is proper on every cycle, so
adjacent windows of distinct identifiers get different colors. -/
example : ((fun _ b _ => b) : Fin 5 → Fin 5 → Fin 5 → Fin 5) 0 1 2 ≠
    ((fun _ b _ => b) : Fin 5 → Fin 5 → Fin 5 → Fin 5) 1 2 3 :=
  window_colors_differ (a := 0) (b := 1) (cc := 2) (d := 3)
    (fun _ b _ => b)
    (fun n _ hn id hid i => by
      have hone : (1 : Fin n).val = 1 := by
        rw [Fin.coe_ofNat_eq_mod]
        exact Nat.mod_eq_of_lt (by omega)
      have hne : i + 1 ≠ i := by
        intro h
        have hi := i.isLt
        have hv := congrArg Fin.val h
        rw [Fin.val_add, hone] at hv
        rcases Nat.lt_or_ge (i.val + 1) n with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hv
          omega
        · have he : i.val + 1 = n := by omega
          rw [he, Nat.mod_self] at hv
          omega
      exact (hid.ne hne).symm) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end Cslib.Distributed.WindowIndistinguishabilityTests

end
