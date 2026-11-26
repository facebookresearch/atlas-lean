# HyperPlonk: Plonk over the Boolean hypercube with linear-time prover

Consider a Plonkish constraint system: a fixed gate polynomial applied row by row to the wire values of $n=2^{\mu}$ gates, together with copy constraints requiring the wire values to be invariant under a fixed permutation of the wire positions. Indexing the gates by the Boolean hypercube $\{0,1\}^{\mu}$ and encoding the wire values as multilinear polynomials, the gate constraint becomes a zero-check and the copy constraints a hypercube product check. Compiled with a multilinear polynomial commitment scheme and batched evaluation openings, this yields a zkSNARK (HyperPlonk) whose prover runs in time $O(n)$ field operations plus the commitment cost, with no FFTs, and which supports custom gates of high degree $d$ with prover cost $O(nd\log^{2}d)$ field operations for the sum-check.

## Proof sketch

Each check is a sum-check over $\mu$ variables whose prover can be implemented in linear time by folding tables. Degree-$d$ gates raise only the per-round degree of the sum-check polynomial. Batching all final evaluation claims into one opening keeps the commitment cost linear.

## Depends on

- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)

## Proof depends on

- [Product check over the Boolean hypercube with an auxiliary multilinear tree](hypercube-product-check.md)
- [Zero-check reduction to sum-check via the equality polynomial](zerocheck-reduction.md)
- [Compiling polynomial IOPs with polynomial commitments into succinct arguments](piop-compilation.md)

## Sources

- Binyi Chen, Benedikt Bünz, Dan Boneh, Zhenfei Zhang, "HyperPlonk: Plonk with Linear-Time Prover and High-Degree Custom Gates", EUROCRYPT (2023), IACR ePrint 2022/1355.
