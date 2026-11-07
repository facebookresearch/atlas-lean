# Sup bound for Schwartz functions with high-frequency Fourier support

Let
$s \in (\tfrac12, 1]$, and for a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier
transform $\hat f$ let
$\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} |\hat f(\xi)|^2 \, d\xi \right)^{1/2}$
be its homogeneous Sobolev seminorm. There is a constant $C_2 > 0$ such that for every real
$A > 0$ and every Schwartz function $f : \mathbb{R} \to \mathbb{C}$ whose Fourier transform has
closed support contained in $\mathbb{R} \setminus [-A, A]$,

$$
\sup_{x \in \mathbb{R}} |f(x)| \le C_2 \, A^{-s + \frac12} \, \|f\|_{\dot H^s}.
$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), `benchmark/level2/ma_proofbench_l2_05.lean` at openbmb/ma-proofbench@31bab4c.
