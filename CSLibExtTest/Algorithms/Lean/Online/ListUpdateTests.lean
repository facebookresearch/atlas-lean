/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.ListUpdate
public meta import CSLibExt.Algorithms.Lean.Online.ListUpdate

/-!
# List update tests

Executed fixtures: on 200 pseudo-random request sequences over 5 items, move-to-front's cost is
compared with the best static list (the minimum over all 120 orders): `MTF + m ≤ 2 STATIC + inv`;
against the offline algorithm that follows move-to-front's own lists (rearrangement charged by
`inv`), `MTF + m ≤ 2 OFF`; and against random offline lists with random free exchanges. A free
exchange costs `3` where the paid move costs `4`. The lower-bound adversary (always request the
last item) makes move-to-front and a frozen list pay `ℓ` per request for `ℓ = 2..6`, while `M`
or its reverse pays at most `(ℓ + 1) / 2` on average. Each run throws on a violation. Closed
checks instantiate the theorems, including the lower bound at ratio `3 / 2`, additive `100`, on
5 items.
-/

namespace Cslib.Algorithms.Lean.Online.ListUpdate

private meta def items : List ℕ := [0, 1, 2, 3, 4]

/-- Move-to-front's lists along a request sequence. -/
private meta def mtfLists : List ℕ → List ℕ → List (List ℕ)
  | L, [] => [L]
  | L, x :: σ => L :: mtfLists (mtf L x) σ

#eval do
  let perms := items.permutations
  let mut s := 3
  let mut worst : ℕ × ℕ := (0, 1)
  for _ in [0:200] do
    let mut σ : List ℕ := []
    for _ in [0:30] do
      s := (s * 1103515245 + 12345) % 2147483648
      σ := σ ++ [s / 13 % 5]
    let m := mtfCost items σ
    let best := perms.foldl (fun b L => min b (staticCost L σ)) (staticCost items σ)
    let bestL := (perms.find? fun L => staticCost L σ == best).getD items
    unless m + σ.length ≤ 2 * best + inv items bestL do
      throw (IO.userError s!"static bound fails on {σ}")
    let Ls := mtfLists items σ
    let off := offlineCost (fun t => Ls.getD t items) σ
    unless m + σ.length ≤ 2 * off do throw (IO.userError s!"offline bound fails on {σ}")
    -- random offline lists (permutations) with random free moves
    let mut Lr : Array (List ℕ) := #[items]
    let mut Jr : Array ℕ := #[]
    for _ in [0:31] do
      s := (s * 1103515245 + 12345) % 2147483648
      Lr := Lr.push (perms.getD (s / 7 % 120) items)
      Jr := Jr.push (s / 11 % 6)
    let offF := offlineCostFree (fun t => Lr.getD t items) (fun t => Jr.getD t 0) σ
    unless m + σ.length ≤ 2 * offF do throw (IO.userError s!"free bound fails on {σ}")
    if m * worst.2 > worst.1 * best then worst := (m, best)
  IO.println s!"200 random sequences over 5 items: MTF + m ≤ 2 STATIC + inv, MTF + m ≤ \
    2 OFF, and MTF + m ≤ 2 OFF_free; worst MTF/STATIC = {worst.1}/{worst.2}"

/-- An algorithm that never moves anything. -/
private meta def frozen (M : List ℕ) : OnlineListUpdate.{0, 0} ℕ M :=
  ⟨Unit, (), fun _ => M, fun _ _ => (), fun _ => List.Perm.refl M⟩

/-- The adversary's sequence costs `A` exactly `ℓ` per request, and `M` or its reverse serves it
at average cost at most `(ℓ + 1) / 2`. -/
private meta def checkAdversary (name : String) {M : List ℕ} (A : OnlineListUpdate.{0, 0} ℕ M)
    (n : ℕ) : IO Unit := do
  let l := M.length
  let σ := A.adversary 0 n A.init
  let c := A.cost A.init σ
  unless c == n * l do throw (IO.userError s!"{name}, l = {l}: cost {c}")
  unless 2 * min (staticCost M σ) (staticCost M.reverse σ) ≤ n * (l + 1) do
    throw (IO.userError s!"{name}, l = {l}: no cheap static list")

#eval do
  for l in [2, 3, 4, 5, 6] do
    let M := List.range l
    checkAdversary "MTF" (mtfOnline M) 60
    checkAdversary "frozen" (frozen M) 60
    let σ := (mtfOnline M).adversary 0 60 (mtfOnline M).init
    unless (mtfOnline M).cost (mtfOnline M).init σ == mtfCost M σ do
      throw (IO.userError s!"mtfOnline disagrees with mtfCost at l = {l}")
  IO.println "adversary, 60 requests, l = 2..6: MTF and the frozen list pay 60 l; M or its \
    reverse pays at most 30 (l + 1); mtfOnline agrees with mtfCost"

-- a free exchange is free: from [0, 1] on requests [1, 1], moving 1 forward costs 3 with a free
-- exchange and 4 when the move is paid
#eval do
  let L : ℕ → List ℕ := fun t => if t = 0 then [0, 1] else [1, 0]
  let paid := offlineCost L [1, 1]
  let free := offlineCostFree L (fun _ => 0) [1, 1]
  unless paid == 4 && free == 3 do throw (IO.userError s!"paid {paid}, free {free}")
  unless mtfCost [0, 1] [1, 1] + 2 ≤ 2 * free do throw (IO.userError "free bound")
  IO.println s!"free exchange: paid model {paid}, free model {free}"

/-! Closed checks -/

example (σ : List ℕ) (hσ : ∀ x ∈ σ, x ∈ [0, 1, 2, 3, 4]) (L : ℕ → List ℕ) (J : ℕ → ℕ)
    (hL : ∀ t, (L t).Perm [0, 1, 2, 3, 4]) (h0 : L 0 = [0, 1, 2, 3, 4]) :
    mtfCost [0, 1, 2, 3, 4] σ + σ.length ≤ 2 * offlineCostFree L J σ :=
  mtfCost_le_free σ (by decide) L J hL h0 hσ


example (σ : List ℕ) (hσ : ∀ x ∈ σ, x ∈ [0, 1, 2, 3, 4]) (L : ℕ → List ℕ)
    (hL : ∀ t, (L t).Perm [0, 1, 2, 3, 4]) (h0 : L 0 = [0, 1, 2, 3, 4]) :
    mtfCost [0, 1, 2, 3, 4] σ + σ.length ≤ 2 * offlineCost L σ :=
  mtfCost_le σ (by decide) L hL h0 hσ

example (A : OnlineListUpdate ℕ [0, 1, 2, 3, 4]) :
    ∃ σ : List ℕ, (∀ x ∈ σ, x ∈ [0, 1, 2, 3, 4]) ∧ ∃ L : ℕ → List ℕ, L 0 = [0, 1, 2, 3, 4] ∧
      (∀ t, (L t).Perm [0, 1, 2, 3, 4]) ∧ 3 * offlineCost L σ + 2 * 100 < 2 * A.cost A.init σ :=
  not_competitive (by decide) (by decide) A (by decide)

#print axioms mtfCost_le
#print axioms mtfCost_le_free
#print axioms not_competitive
#print axioms mtfCost_le_static
#print axioms mtf_step
#print axioms inv_triangle

end Cslib.Algorithms.Lean.Online.ListUpdate
