# Elliptical symmetry is necessary for consistency

**Elliptical symmetry is necessary for consistency** (Paninski 2003, Theorem 1, necessity;
Appendix A.1, Eq. (9)). Let `n ≥ 2` and let `ν` be a probability law on `ℝⁿ` that is centered
(`x_i` integrable with `∫ x_i dν = 0` for each `i`), has finite second moments (`x_i x_j`
integrable for all `i, j`), has positive definite second-moment matrix `Σ = covMatrix ν`, and is
not elliptically symmetric. Then there are a filter `k` with `kᵀ Σ k > 0` and a measurable
nonlinearity `g ≥ 0` with `g(k · x)` and `g(k · x) x` integrable and `∫ g(k · x) dν > 0`, such
that the population spike-triggered average `(∫ g(k · x) dν)⁻¹ ∫ g(k · x) x dν` (the almost sure
limit of `STA_N` under the strong law) is not equal to `c Σ k` for any real `c`.

This is the source's statement after whitening by `Σ^{-1/2}`, which turns "not radially
symmetric" into "not elliptically symmetric" and the direction `v` into `Σ k`. Both
restrictions are needed: for `n = 1` every vector is a multiple of `Σ k ≠ 0`, and a centered law
supported on a line in `ℝ²` is not elliptical but has its population average along `Σ k` for
every such `k` and `g`; positive definiteness of `Σ` excludes such laws.

## Sources

- L. Paninski, "Convergence properties of three spike-triggered analysis techniques", Network: Comput. Neural Syst. 14 (2003) 437–464, Theorem 1 and Appendix A.1, Eq. (9).
