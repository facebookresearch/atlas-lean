# Johnstone's Tracy–Widom limit

Let $q : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable with $q''(s) = s\,q(s) + 2q(s)^3$ for all
$s$ and

$$q(s) \cdot 2\sqrt{\pi}\, s^{1/4} e^{\frac23 s^{3/2}} \to 1 \qquad (s \to \infty),$$

the Hastings–McLeod solution of Painlevé II. Let $n_k, p_k \to \infty$ with $n_k / p_k \to \gamma$ for some
$\gamma \ge 1$, let $X$ be an $n_k \times p_k$ matrix with independent standard Gaussian entries, and let
$\ell_1 = \sup_{\|v\| = 1} \|Xv\|^2$ be the largest eigenvalue of $X^{\mathsf T} X$. Put

$$\mu_k = \bigl(\sqrt{n_k - 1} + \sqrt{p_k}\bigr)^2, \qquad
\sigma_k = \bigl(\sqrt{n_k - 1} + \sqrt{p_k}\bigr)\Bigl(\frac{1}{\sqrt{n_k - 1}} + \frac{1}{\sqrt{p_k}}\Bigr)^{1/3}.$$

Then for every real $s$, the function $x \mapsto q(x) + (x - s)\,q(x)^2$ is integrable on $(s, \infty)$ and

$$\mathbb{P}\Bigl(\frac{\ell_1 - \mu_k}{\sigma_k} \le s\Bigr) \to F_1(s) = \exp\Bigl(-\frac12 \int_s^\infty \bigl(q(x) + (x - s)\,q(x)^2\bigr)\,dx\Bigr)
\qquad (k \to \infty),$$

the Tracy–Widom law of the Gaussian orthogonal ensemble.

## Sources

- I. M. Johnstone, *On the distribution of the largest eigenvalue in principal components analysis*, Ann. Statist.
  29 (2001), 295–327, Theorem 1.1.
- C. A. Tracy and H. Widom, *On orthogonal and symplectic matrix ensembles*, Comm. Math. Phys. 177 (1996), 727–754,
  for $F_1$.
- S. P. Hastings and J. B. McLeod, *A boundary value problem associated with the second Painlevé transcendent and
  the Korteweg–de Vries equation*, Arch. Rational Mech. Anal. 73 (1980), 31–51, for $q$.
