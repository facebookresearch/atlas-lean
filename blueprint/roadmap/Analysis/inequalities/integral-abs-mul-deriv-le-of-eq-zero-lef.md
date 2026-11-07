# Opial's inequality with one boundary condition

Let $\alpha \le \beta$ be real numbers and
let $f : \mathbb{R} \to \mathbb{R}$ be continuously differentiable on $[\alpha, \beta]$ with
$f(\alpha) = 0$. Then

$$\int_\alpha^\beta |f(x) f'(x)|\,dx \le \frac{\beta - \alpha}{2} \int_\alpha^\beta |f'(x)|^2\,dx.$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in real analysis), `benchmark/level1/ma_proofbench_l1_76.lean` at openbmb/ma-proofbench@31bab4c.
