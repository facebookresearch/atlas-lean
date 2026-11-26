# Bernstein-type bound for the derivative of a band-limited Schwartz function

Let
$s \in (\tfrac12, 1]$. For a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ write
$\hat f(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x\xi}\,dx$ for its Fourier transform and
$\|f\|_{\dot H^s} = \left(\int_{\mathbb{R}} |\xi|^{2s} |\hat f(\xi)|^2\,d\xi\right)^{1/2}$ for
its homogeneous Sobolev seminorm. There is a constant $C_1 > 0$ such that for every real
$A \ge 0$ and every Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with $\hat f(\xi) = 0$
whenever $|\xi| > A$,

$$\sup_{x \in \mathbb{R}} |f'(x)| \le C_1 A^{3/2 - s}\, \|f\|_{\dot H^s}.$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), problem `ma_proofbench_l2_00`.
