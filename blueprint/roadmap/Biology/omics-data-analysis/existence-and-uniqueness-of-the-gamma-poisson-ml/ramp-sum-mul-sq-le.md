# The ramp sum divided by the squared argument is antitone

For every natural number `k` and reals `0 < x ≤ y`, the [ramp sum](ramp-sum.md) satisfies
`x² R_k(y) ≤ y² R_k(x)`: the function `u ↦ R_k(u) / u²` is antitone on `(0, ∞)`.

Since `R_k` has right derivative `G_k(u)`, the number of the points `0, 1, …, k - 1` that are at
most `u`, this is equivalent to `u G_k(u) ≤ 2 ∫₀ᵘ G_k` for every `u > 0`. In this form it is the
inequality `∫₀ᵘ G ≥ (u / 2) G(u)` that Levin and Reeds (1977, §3.1, p. 85) use in the proof of their
Theorem 2, "a simple modification of Lemma 2.2" (their eq. 2.4 concerns the convolved measure `G*`).
