# Bernstein inequality for Schwartz functions with Fourier support of finite measure

Fix $n \in \mathbb{N}$. For a Schwartz function $f : \mathbb{R}^n \to \mathbb{C}$ write
$\hat f(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$ for its Fourier
transform, and write $|E|$ for the Lebesgue measure of a set $E \subseteq \mathbb{R}^n$. There
is a constant $C > 0$ such that for every Borel set $E \subseteq \mathbb{R}^n$ with
$|E| < \infty$, all $p, q \in [1, \infty]$ with $p \le q$ and $p \le 2$, and every Schwartz
function $f : \mathbb{R}^n \to \mathbb{C}$ whose Fourier transform has closed support
$\overline{\{\xi : \hat f(\xi) \ne 0\}}$ contained in $E$,

$$\|f\|_{L^q(\mathbb{R}^n)} \le C\, |E|^{1/p - 1/q}\, \|f\|_{L^p(\mathbb{R}^n)},$$

where $1/q = 0$ for $q = \infty$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Distributions, generalized functions, distribution spaces), problem `ma_proofbench_l2_47`.
