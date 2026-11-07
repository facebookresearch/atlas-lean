# A bounded integrable function is square integrable

Let $d$ be a natural number, let
$M \ge 0$, and let $f \colon \mathbb{R}^d \to \mathbb{R}$ satisfy $|f(x)| \le M$ for every
$x \in \mathbb{R}^d$. If $f \in L^1(\mathbb{R}^d)$, then $f \in L^2(\mathbb{R}^d)$ and

$$\|f\|_{L^2(\mathbb{R}^d)} \le M^{1/2} \, \|f\|_{L^1(\mathbb{R}^d)}^{1/2},$$

where the spaces and norms are taken with respect to Lebesgue measure.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear function spaces and their duals), `benchmark/level1/ma_proofbench_l1_41.lean` at openbmb/ma-proofbench@31bab4c.
