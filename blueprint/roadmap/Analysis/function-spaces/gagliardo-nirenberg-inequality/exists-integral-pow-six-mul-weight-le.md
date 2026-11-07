# A weighted $L^6$ bound with a slowly varying weight

There is a constant $C > 0$ with the
following property. Let $\theta : \mathbb{R} \to \mathbb{R}$ be continuously differentiable, with
$\theta(x) > 0$ for every $x$ and $\|\theta'/\theta\|_{L^\infty(\mathbb{R})} \le 1$, and let
$u : \mathbb{R} \to \mathbb{R}$ be smooth with compact support. Then

$$\int_{\mathbb{R}} u(x)^6\,\theta(x)\,dx \le C\,\|u\|_{L^2(\mathbb{R})}^4
\int_{\mathbb{R}} \left(|u'(x)|^2 + |u(x)|^2\right)\theta(x)\,dx.$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities in real analysis), `benchmark/level2/ma_proofbench_l2_67.lean` at openbmb/ma-proofbench@31bab4c.
