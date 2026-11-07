# The Laplace transform is bounded on $L^p((0,\infty))$ exactly when $p = 2$

For a real
function $f$ on $\mathbb{R}$ let

$$Lf(s) = \int_0^\infty e^{-xs} f(x)\,dx \qquad (s \in \mathbb{R}).$$

Let $p \in [1,\infty]$. Then $p = 2$ if and only if there is a constant $C$ with $0 < C < \infty$
such that every real function $f \in L^p([0,\infty))$ satisfies $Lf \in L^p([0,\infty))$ and
$\|Lf\|_{L^p([0,\infty))} \le C\,\|f\|_{L^p([0,\infty))}$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral, integro-differential, and pseudodifferential operators), `benchmark/level2/ma_proofbench_l2_31.lean` at openbmb/ma-proofbench@31bab4c.
