# Nernst equilibrium from zero Nernst–Planck flux

Let `D`, `R`, `T`, `z`, `F` and `L` be real numbers with `D ≠ 0`, `R T ≠ 0`, `z F ≠ 0` and
`L ≥ 0`, and consider a membrane `[0, L]` with the inside at `x = 0` and the outside at `x = L`.
Let `c`, `c'`, `φ` and `φ'` be real functions such that, at every `x ∈ [0, L]`:

- the concentration is positive, `c(x) > 0`;
- `c` has derivative `c'(x)` and `φ` has derivative `φ'(x)` within `[0, L]` (one-sided at the
  ends);
- the [Nernst–Planck flux](nernst-planck-flux.md) vanishes:
  `-D (c'(x) + (z F / (R T)) c(x) φ'(x)) = 0`.

Then the membrane voltage is the [Nernst potential](nernst-potential.md) of the boundary
concentrations:

`φ(0) - φ(L) = (R T / (z F)) log (c(L) / c(0))`.

For `L = 0` both sides are `0`. The proof shows that `log c + (z F / (R T)) φ` has zero derivative
within `[0, L]`, hence is constant there.
