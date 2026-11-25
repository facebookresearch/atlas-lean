# Patterson's dilogarithm

For a real number `x`, let

`dilog(x) = Σ_{k ≥ 1} (1 - x)^k / k²`,

where the sum of a series that is not summable is `0`. The series converges for `0 ≤ x ≤ 2`, where
`dilog(x) = Li₂(1 - x)` for the classical dilogarithm `Li₂`, and `dilog(x) = 0` for `x < 0` and for
`x > 2`. The intended domain is `0 < x < 1`, where `dilog` is the function of Patterson's Equation
16: it agrees there with his definition `∫₁ˣ log t / (1 - t) dt`
([integral form](patterson-dilog-eq-integral.md)), with `dilog(1) = 0` and derivative
`log x / (1 - x)`.

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
