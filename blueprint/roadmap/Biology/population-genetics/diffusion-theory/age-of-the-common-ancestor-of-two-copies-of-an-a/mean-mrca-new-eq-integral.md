# Patterson's Equation 16 derived from Theorem 4

For `y ∈ (0, 1)`,
`M₁(y) = y ∫₀¹ G_C(x, y) / x dx`. The integral representation is Patterson's
(p. 1103); the closed form `meanMrcaNew` is obtained from it by the two
antiderivatives `hasDerivAt_antideriv_aux1` (below the diagonal) and
`-C / x - C log x` with `C = 2 a₁(y) / ((1 - y) y)` (above), the reflection
formula `pattersonDilog_reflection`, and `pattersonDilog_zero`. In the diffusion
reading, the right side is `∫₀^∞ B(t) dt` for his Equation 15; the weight `y / x`
is the new-allele frequency density of Theorem 3 (here `neutralGreen`): it equals
`G_K(ε, x) / G_K(ε, y) = (2ε / x) / (2ε / y)` once `ε < min x y`, and the
coalescence rate `1 / x` acts through the killing in `G_C`.
