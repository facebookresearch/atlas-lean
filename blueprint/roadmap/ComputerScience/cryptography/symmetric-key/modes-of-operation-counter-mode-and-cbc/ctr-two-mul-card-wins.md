# Fresh counter ranges give an exact half guessing chance

Let `N ≠ 0`, `ℓ ≤ N`, and `Y` a finite additive group. If the challenge
counter range starting at `rs` is fresh with respect to the query counters `ρ
: Fin q → ZMod N`, then for every adversary computation `c`, exactly half of
the pairs `(f, b)` of a function `f : ZMod N → Y` and a challenge bit `b` lead
the adversary to guess `b`: twice the number of winning pairs equals the
number of all pairs.
