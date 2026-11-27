# Spark: committing to sparse multilinear polynomials via memory checking

Let $M:\{0,1\}^{s}\times\{0,1\}^{s}\to\mathbb{F}$ have $m$ nonzero entries listed as $(\mathrm{row}(k),\mathrm{col}(k),\mathrm{val}(k))_{k< m}$. Then for all $r_x,r_y\in\mathbb{F}^{s}$,

$$
\widetilde{M}(r_x,r_y)=\sum_{k< m}\mathrm{val}(k)\,\widetilde{\mathrm{eq}}(r_x,\mathrm{row}(k))\,\widetilde{\mathrm{eq}}(r_y,\mathrm{col}(k)).
$$

Committing to the three dense vectors of length $m$, the prover proves an evaluation by committing to $e_x(k)=\widetilde{\mathrm{eq}}(r_x,\mathrm{row}(k))$ and $e_y(k)$, running a sum-check on the displayed sum, and proving with offline memory checking that $e_x,e_y$ are correct reads from the tables $(\widetilde{\mathrm{eq}}(r_x,b))_{b}$ and $(\widetilde{\mathrm{eq}}(r_y,b))_b$, which the verifier can evaluate at any point in $O(s)$ time. The cost is $O(m+2^{s})$ field operations.

## Proof sketch

The identity is the multilinear-extension formula applied to the sparse support. Memory checking certifies that each committed $e_x(k)$ equals the table entry at address $\mathrm{row}(k)$; the table's multilinear extension at a random point is $\widetilde{\mathrm{eq}}(r_x,\cdot)$ evaluated there, computable by the verifier, so no commitment to the table is needed.

## Depends on

- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Offline memory checking with timestamps](offline-memory-checking.md)

## Proof depends on

- [Multiset equality certifies read-correctness of memory](memory-checking-soundness.md)
- [Multiset equality via randomized product fingerprints](multiset-fingerprint.md)
- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Sources

- Srinath Setty, "Spartan: Efficient and General-Purpose zkSNARKs without Trusted Setup", CRYPTO (2020), IACR ePrint 2019/550.
- Srinath Setty, Justin Thaler, Riad Wahby, "Unlocking the Lookup Singularity with Lasso", EUROCRYPT (2024), IACR ePrint 2023/1216.
