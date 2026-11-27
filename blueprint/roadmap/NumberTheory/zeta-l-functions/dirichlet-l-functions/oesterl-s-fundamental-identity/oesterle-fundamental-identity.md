# Oesterlé's fundamental identity `J(U) = -J(U*)`

**Oesterlé's fundamental identity `J(U) = -J(U*)`.**
Let $d > 0$ and $M > 0$ be real numbers and put $\gamma(s) = M^s \Gamma(s)^2$. Let
$\Psi(s) = \sum_{n \ge 1} \psi_n n^{-s}$ be a Dirichlet series converging absolutely for
$\operatorname{Re} s > 1$, and let $G(s) = \sum_{n \ge 1} g_n n^{-s}$ be a Dirichlet series
converging absolutely for $\operatorname{Re} s > 3/2$ that is an Euler product
$G = \prod_p G_p$ in which, for each prime $p$,

$$G_p(s) = \frac{(1 + \alpha_p p^{-s})(1 + \beta_p p^{-s})}
{(1 + \alpha'_p p^{-s})(1 + \beta'_p p^{-s})}$$

with complex numbers $\alpha_p, \beta_p, \alpha'_p, \beta'_p$ of absolute value at most
$\sqrt p$ (Oesterlé's condition (C2)). Suppose (condition (C3)) that the function
$F(s) = d^s \gamma(s) \Psi(s) G(s)$, $\operatorname{Re} s > 3/2$, extends to an entire function on
$\mathbb{C}$ that is of rapid decay at infinity in vertical strips (for every $k \ge 0$ and every
bounded interval $I$, $|F(\sigma + it)| |t|^k$ stays bounded as $|t| \to \infty$, uniformly for
$\sigma \in I$), satisfies $F(2 - s) = F(s)$ and has a zero of order at least $3$ at $s = 1$, that
is, $F(s) = (s - 1)^3 F_1(s)$ with $F_1$ entire. Suppose also, as in Oesterlé's condition (C4),
that $\Psi$ extends holomorphically to a neighbourhood of the half-plane
$\operatorname{Re} s \ge 1$ and that $\gamma\Psi$ is of rapid decay at infinity in every vertical
strip of that half-plane. Then for every $\sigma > 3/2$ (Oesterlé's (3.1.1))

$$\int_{\sigma - i\infty}^{\sigma + i\infty} d^{s-1} \gamma(s) \Psi(s) G(s) (s - 1)^{-3}
\,\frac{ds}{2\pi i} = 0.$$

For a real number $U \ge 1$ put (3.1.2)–(3.1.3)

$$G(U, s) = \prod_{p < U} G_p(s), \qquad
G(U^*, s) = G(s) - G(U, s) = G(U, s)\Big(\Big(\prod_{p \ge U} G_p(s)\Big) - 1\Big),$$

and let $J(U)$ and $J(U^*)$ be the integrals of (3.1.1) with $G(s)$ replaced by $G(U, s)$ and by
$G(U^*, s)$. These integrals converge absolutely and (3.1.4) $J(U) = -J(U^*)$.

Here $\Psi = $ `LSeries ψ`, $G = $ `LSeries g`, $G_p = $ `eulerFactor α β α' β' p`,
$G(U, \cdot) = $ `partialEuler α β α' β' U`, the integrals are `oesterleIntegral`, and the
holomorphic extension of $\Psi$ is `Ψ'` on the open set `V`. The identity of (3.1.3) is stated
for $\operatorname{Re} s > 3/2$ and every real $U$.

## Sources

- J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki exposé 631, Astérisque 121–122 (1985), 309–323, §3, conditions (C1)–(C4) (p. 314), and §3.1, (3.1.1)–(3.1.4) (pp. 314–315).
