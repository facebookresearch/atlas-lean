# HyperPlonk: Plonk over the Boolean hypercube with linear-time prover

Replacing the multiplicative subgroup by the Boolean hypercube $\{0,1\}^{\mu}$ ($n=2^{\mu}$ gates) and univariate polynomials by multilinear ones, the Plonkish gate constraint becomes a zero-check and the copy constraints a hypercube product check. Compiled with a multilinear polynomial commitment scheme and batched evaluation openings, this yields a zkSNARK (HyperPlonk) whose prover runs in time $O(n)$ field operations plus the commitment cost, with no FFTs, and which supports custom gates of high degree $d$ with prover cost $O(nd\log^{2}d)$ field operations for the sum-check.

## Proof sketch

Each check is a sum-check over $\mu$ variables whose prover can be implemented in linear time by folding tables. Degree-$d$ gates raise only the per-round degree of the sum-check polynomial. Batching all final evaluation claims into one opening keeps the commitment cost linear.

## Depends on

- [Product check over the Boolean hypercube with an auxiliary multilinear tree](hypercube-product-check.md)
- [Zero-check reduction to sum-check via the equality polynomial](zerocheck-reduction.md)
- [Compiling polynomial IOPs with polynomial commitments into succinct arguments](piop-compilation.md)
- [PLONK gate equations with copy constraints](plonk-constraint-system.md)

## Proof depends on

- [Product check over the Boolean hypercube with an auxiliary multilinear tree](hypercube-product-check.md)
- [Compiling polynomial IOPs with polynomial commitments into succinct arguments](piop-compilation.md)

## Sources

- Binyi Chen, Benedikt Bünz, Dan Boneh, Zhenfei Zhang, "HyperPlonk: Plonk with Linear-Time Prover and High-Degree Custom Gates", EUROCRYPT (2023), IACR ePrint 2022/1355.
