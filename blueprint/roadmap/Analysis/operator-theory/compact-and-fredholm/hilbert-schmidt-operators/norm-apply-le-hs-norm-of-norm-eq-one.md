# The Hilbert–Schmidt norm bounds an operator on unit vectors

Let $H$ be a real Hilbert
space, let $T : H \to H$ be a bounded linear operator, and let $(u_n)_{n \in \mathbb{N}}$ be an
orthonormal basis of $H$ indexed by the natural numbers. Let
$\|T\|_{\mathrm{HS}} = \bigl(\sum_{n} \|T u_n\|^2\bigr)^{1/2} \in [0, \infty]$ be the
Hilbert–Schmidt norm of $T$ computed in this basis; it is $\infty$ when the series diverges.
Then $\|Tx\| \le \|T\|_{\mathrm{HS}}$ for every $x \in H$ with $\|x\| = 1$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Special classes of linear operators), `benchmark/level2/ma_proofbench_l2_68.lean` at openbmb/ma-proofbench@31bab4c.
