# Kimura Prob

The **Kimura two-parameter transition matrix** in terms of the composite parameters
`a = α t` (transition rate times time) and `b = β t` (rate of each of the two transversions
times time), in the order `A, C, G, T`:

* `1/4 + 1/4 · e^{-4b} + 1/2 · e^{-2(a + b)}` on the diagonal,
* `1/4 + 1/4 · e^{-4b} - 1/2 · e^{-2(a + b)}` for a transition (`A ↔ G`, `C ↔ T`),
* `1/4 - 1/4 · e^{-4b}` for each transversion.

These are the formulas of Kimura (1980), eqs. (5)–(6).
