# The homogeneous Sobolev seminorm controls the Hölder seminorm

Let $s \in (\tfrac12, 1]$,
and for a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier transform $\hat f$ let
$\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} |\hat f(\xi)|^2 \, d\xi \right)^{1/2}$
be its homogeneous Sobolev seminorm. There is a constant $C_3 > 0$ such that for every Schwartz
function $f : \mathbb{R} \to \mathbb{C}$,

$$
\sup_{x \ne y} \frac{|f(x) - f(y)|}{|x - y|^{s - \frac12}} \le C_3 \, \|f\|_{\dot H^s}.
$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), problem `ma_proofbench_l2_21`.
