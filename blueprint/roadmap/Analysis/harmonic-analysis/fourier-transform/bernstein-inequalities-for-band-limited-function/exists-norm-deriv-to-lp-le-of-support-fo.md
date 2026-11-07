# Bernstein inequality for band-limited Schwartz functions

For a Schwartz function
$f : \mathbb{R} \to \mathbb{C}$ write $\hat f(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x\xi}\,dx$
for its Fourier transform. There is a constant $C_0 > 0$ such that for every $p \in [1, \infty]$
and every Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with $\hat f(\xi) = 0$ whenever
$|\xi| \ge 1$,

$$\|f'\|_{L^p(\mathbb{R})} \le C_0 \|f\|_{L^p(\mathbb{R})}.$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), `benchmark/level2/ma_proofbench_l2_70.lean` at openbmb/ma-proofbench@31bab4c.
