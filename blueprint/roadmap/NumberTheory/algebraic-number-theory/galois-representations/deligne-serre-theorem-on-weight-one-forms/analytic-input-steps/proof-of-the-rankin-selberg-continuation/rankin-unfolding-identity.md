# Rankin's unfolding identity on Γ₀(N)

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with $\varepsilon(-1) = (-1)^k$, and let
$f = \sum_{n \ge 1} a_n q^n$ and $g = \sum_{n \ge 1} b_n q^n$, $q = e^{2\pi i z}$, be cusp forms of
[type $(k, \varepsilon)$ on $\Gamma_0(N)$](../../modular-forms-of-type-k-epsilon.md). For
$z = x + iy$ in the upper half-plane and $\operatorname{Re}(s) > 1$ let

$$E_N(z, s) = \sum_{\gamma \in \Gamma_\infty \backslash \Gamma_0(N)} \operatorname{Im}(\gamma z)^s = y^s + \sum_{c > 0,\ N \mid c} \ \sum_{d \in \mathbb{Z},\ (c, d) = 1} \frac{y^s}{|cz + d|^{2s}},$$

where $\Gamma_\infty = \{ \pm \left(\begin{smallmatrix} 1 & n \\ 0 & 1 \end{smallmatrix}\right) : n \in \mathbb{Z} \}$, be the Eisenstein series of
$\Gamma_0(N)$ at the cusp $\infty$, and let $D$ be a fundamental domain for $\Gamma_0(N)$, with the measure
$d\mu = dx\, dy / y^2$. Then for $\operatorname{Re}(s) > 1$ the series $E_N(z, s)$ converges absolutely, the function
$f(z) \overline{g(z)} y^k E_N(z, s)$ is integrable on $D$, the Dirichlet series $\sum_n a_n \overline{b_n}\, n^{-(s+k-1)}$ converges
absolutely, and

$$\int_D f(z)\, \overline{g(z)}\, y^k E_N(z, s)\, d\mu(z) = (4\pi)^{-(s+k-1)}\, \Gamma(s + k - 1) \sum_{n \ge 1} a_n \overline{b_n}\, n^{-(s+k-1)}.$$

In particular $\sum_n |a_n|^2 n^{-s}$ converges for $\operatorname{Re}(s) > k$.

Ogg (§2) and Li (§4) derive this, following Rankin, for $\varepsilon = 1$; their argument uses only that
$f(z) \overline{g(z)} y^k$ is invariant under $\Gamma_0(N)$, which holds for every $\varepsilon$ since $|\varepsilon(d)| = 1$. The
cosets $\Gamma_\infty \gamma$ correspond to the pairs $\pm(c, d)$ of coprime integers with $N \mid c$, with representatives
$(0, 1)$ and the $(c, d)$ with $c > 0$, and $\operatorname{Im}(\gamma z) = y/|cz + d|^2$; so the integral over $D$ unfolds into
one over the strip $0 \le x \le 1$, $y > 0$. There the integral of the product of the two Fourier expansions over $x$ is
$\sum_n a_n \overline{b_n}\, e^{-4\pi n y}$, and Euler's integral
$\int_0^\infty e^{-4\pi n y}\, y^{s+k-2}\, dy = \Gamma(s+k-1)\, (4\pi n)^{-(s+k-1)}$ gives the right side. For $g = f$ and real
$s > 1$ every term is nonnegative, so the identity also shows that $\sum_n |a_n|^2 n^{-\sigma}$ is finite for $\sigma > k$;
with $|a_n \overline{b_n}| \le (|a_n|^2 + |b_n|^2)/2$ this gives the absolute convergence in general.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](../../modular-forms-of-type-k-epsilon.md), for cusp forms of type $(k, \varepsilon)$
- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the cusp forms of weight $k$ on $\Gamma_1(N)$
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the absolute convergence of $E_N(z, s)$ for $\operatorname{Re}(s) > 1$, locally uniformly in $z$, by comparison with the
  series $\sum_{(m, n) \ne (0, 0)} y^{\sigma} |m + n z|^{-2\sigma}$ of the
  [Epstein zeta function](../../../../../modular-forms-q-series/modular-forms/epstein-zeta-binary-functional-equation.md);
- the boundedness of $y^{k/2} |f(z)|$ on the upper half-plane for a cusp form $f$ on $\Gamma_1(N)$, and the exponential
  decay of $f(x + iy)$ as $y \to \infty$, which make $f \overline{g} y^k E_N(z, s)$ integrable on $D$ for
  $\operatorname{Re}(s) > 1$;
- the unfolding itself: the invariance of $f(z) \overline{g(z)} y^k\, d\mu$ under $\Gamma_0(N)$, the tiling of the strip by the
  translates $\gamma D$ for $\gamma$ in a set of representatives of $\Gamma_\infty \backslash \Gamma_0(N)$, and Tonelli's and
  Fubini's theorems;
- the orthogonality $\int_0^1 e^{2\pi i (m - n) x}\, dx = \delta_{mn}$ and Euler's integral for $\Gamma$.

## Sources

- A. P. Ogg, *On a convolution of L-series*, Invent. Math. 7 (1969), 297–312: §2, p. 302 (formula (1)) and p. 303 (the
  coset representatives, formula (2) and the function $F_N(\tau, s)$, with $E_N(z, s) = y^s F_N(z, s)$); §1, p. 298, for
  the form $\delta(f, g) = y^{k-2} f(\tau) \overline{g(\tau)}\, dx\, dy$.
- W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315: §4, p. 312.
- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Démonstration 5.2, p. 518, for the convergence of
  $\sum |a_n|^2 n^{-s}$ on $\operatorname{Re}(s) > k$, which they attribute to Rankin.
