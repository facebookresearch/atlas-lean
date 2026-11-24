# The continuum of unstable wavenumbers is infinite

If `d_u, d_v > 0`, `tr J < 0` and
`2 √(d_u d_v det J) < d_v f_u + d_u g_v`, infinitely many real wavenumbers `k` are unstable: every
`k` with `k² ∈ (max q₋ 0, q₊)` is. Since `Real.sqrt` sends negative arguments to `0`, these
hypotheses do not include `0 < det J`, so they are a dispersion-band condition, not stability
without diffusion; adding `0 < det J` gives Turing's criterion (as in `continuum_vs_neumann`).
Contrast `finite_setOf_isUnstableMode_neumannWavenumber`: on a finite domain only finitely many
Neumann modes are unstable.
