---
article_id: af_951a3b88d925b682639cf75d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem
---

# Prime Number Theorem

`Nat.primeCounting` satisfies `π(n) ~ n / log n` as `n → ∞`, i.e. `IsEquivalent atTop (fun n =>
(Nat.primeCounting n : ℝ)) (fun n => (n : ℝ) / Real.log n)`. Source: J. Hadamard and C. de la
Vallée Poussin, 1896 independent proofs of PNT; original: Hadamard, Sur la distribution des zéros
de ζ, Bull. Soc. Math. France 24 (1896) 199–220, de la Vallée Poussin, Recherches analytiques,
Ann. Soc. Sci. Bruxelles 20 (1896); textbook in Apostol, Introduction to Analytic Number Theory

## Depends on

This node has no prerequisites.

## Proof depends on

- [Monotone Integral Criterion](../../../Analysis/MathlibExt/part-01/asymptotics/is-equivalent-id-of-monotone-on-of-tends.md)
- [Abs normalized Theta Error le](../part-02/prime-counting/part-01/normalized-theta-error/abs-normalized-theta-error-le.md)
- [Has Laplace normalized Theta Error](../part-02/prime-counting/part-01/laplace-theta-continuation/has-laplace-normalized-theta-error.md)
- [Measurable normalized Theta Error](../part-02/prime-counting/part-01/normalized-theta-error/measurable-normalized-theta-error.md)
- [Normalized Theta Error](../part-02/prime-counting/part-01/laplace-theta-continuation/normalized-theta-error.md)
- [Normalized Theta Error Continuation](../part-02/prime-counting/part-01/laplace-theta-continuation/normalized-theta-error-continuation.md)
- [Normalized Theta Error Continuation analytic On](../part-02/prime-counting/part-01/laplace-theta-continuation/normalized-theta-error-continuation-anal.md)
- [Prime Counting is Equivalent of theta is Equivalent](../part-02/prime-counting/part-01/chebyshev/prime-counting-is-equivalent-of-theta-is.md)
- [Newman Tauberian](../../../Analysis/MathlibExt/part-01/laplace-transform/newman-tauberian.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeNumberTheorem](../../../../sources/v2/MathlibExt.md)
