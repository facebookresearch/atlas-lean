# Max Segment Score

The maximal segment score `Mₙ = max_{0 ≤ i ≤ j ≤ n} (x i + ⋯ + x (j - 1))` of the first `n`
scores `x 0, …, x (n - 1)`. The empty segment is allowed, so `Mₙ ≥ 0`.

This is the same quantity as T49's `maxSegScore (List.ofFn fun i : Fin n => x i)`; it is restated
here because T49 is not on `main`. TODO: prove the equality once T49 lands.
