# Heisenberg uncertainty inequality with shifted moments

For a complex-valued Schwartz
function $f$ on $\mathbb{R}$, write
$\hat{f}(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x \xi}\, dx$ for its Fourier transform. There is
a constant $C > 0$ such that for all real numbers $c$ and $d$ and every complex-valued Schwartz
function $f$ on $\mathbb{R}$,

$$
\left(\int_{\mathbb{R}} |f(x)|^2\, dx\right)^2 \le C
\left(\int_{\mathbb{R}} (x - c)^2 |f(x)|^2\, dx\right)
\left(\int_{\mathbb{R}} (\xi - d)^2 |\hat{f}(\xi)|^2\, d\xi\right).
$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Distributions, generalized functions, distribution spaces), problem `ma_proofbench_l2_46`.
