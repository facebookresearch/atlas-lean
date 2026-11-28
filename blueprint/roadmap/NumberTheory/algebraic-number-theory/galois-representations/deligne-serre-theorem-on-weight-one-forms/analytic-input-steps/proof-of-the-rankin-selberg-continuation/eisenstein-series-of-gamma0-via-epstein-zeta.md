# The Eisenstein series of Γ₀(N) at the cusp ∞ through Epstein zeta functions

Let $N \ge 1$. For $z = x + iy$ in the upper half-plane and $\operatorname{Re}(s) > 1$ let

$$E_N(z, s) = y^s + \sum_{c > 0,\ N \mid c} \ \sum_{d \in \mathbb{Z},\ (c, d) = 1} \frac{y^s}{|cz + d|^{2s}}$$

be the Eisenstein series of $\Gamma_0(N)$ at the cusp $\infty$, let
$\zeta_N(s) = \sum_{n \ge 1,\ (n, N) = 1} n^{-s} = \prod_{p \nmid N} (1 - p^{-s})^{-1}$, and for $w$ in the upper half-plane let

$$Z(w, s) = \sum_{(m, n) \ne (0, 0)} \frac{\operatorname{Im}(w)^s}{|m + n w|^{2s}} \qquad (\operatorname{Re} s > 1)$$

be the [Epstein zeta function](../../../../../modular-forms-q-series/modular-forms/epstein-zeta-binary-functional-equation.md) of the
form $Q_w$, with its completion $\Lambda(w, s) = \pi^{-s} \Gamma(s) Z(w, s)$. Then, with $\mu$ the Möbius function,

$$2\, \zeta_N(2s)\, E_N(z, s) = N^{-s} \sum_{d \mid N} \mu(d)\, d^{-s}\, Z(Nz/d, s) \qquad (\operatorname{Re} s > 1).$$

Consequently, for each $z$, $\zeta_N(2s) E_N(z, s)$ extends to a meromorphic function of $s \in \mathbb{C}$ whose only pole is a
simple pole at $s = 1$, with residue $\pi \varphi(N)/(2N^2)$, where $\varphi$ is Euler's function; and

$$2\, \pi^{-s}\, \Gamma(s)\, \zeta_N(2s)\, E_N(z, s) = N^{-s} \sum_{d \mid N} \mu(d)\, d^{-s}\, \Lambda(Nz/d, s), \qquad \Lambda(w, s) = \Lambda(w, 1 - s).$$

Ogg proves the identity as follows. Both signs of the pair $(c, d)$ counted, $2 E_N(z, s)$ is the sum of
$y^s |cz + d|^{-2s}$ over the coprime pairs with $N \mid c$; multiplying by $\zeta_N(2s) = \sum_{(r, N) = 1} r^{-2s}$ gives the
sum over all pairs $(c, d) \ne (0, 0)$ with $N \mid c$ and $(d, N) = 1$, each once as $r$ times a coprime pair. Inserting
$\sum_{d' \mid (d, N)} \mu(d')$, which is $1$ when $(d, N) = 1$ and $0$ otherwise, and replacing $d$ by $d' d$ gives
$\sum_{d' \mid N} \mu(d') d'^{-2s} \sum_{(m, n) \ne (0, 0)} y^s |m (N/d') z + n|^{-2s}$, and the inner sum is
$(d'/N)^s Z(Nz/d', s)$ since $\operatorname{Im}(Nz/d') = Ny/d'$. The rest follows from the continuation of $Z(w, s)$, whose only
pole is a simple pole at $s = 1$ with residue $\pi$ for every $w$, from $\sum_{d \mid N} \mu(d)/d = \varphi(N)/N$, and from the
functional equation of $\Lambda$.

## Depends on

- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)
- [Functional equation of the Epstein zeta function of a binary form](../../../../../modular-forms-q-series/modular-forms/epstein-zeta-binary-functional-equation.md), for $Z(w, s)$ and $\Lambda(w, s)$

## Proof depends on

- [Functional equation of the Epstein zeta function of a binary form](../../../../../modular-forms-q-series/modular-forms/epstein-zeta-binary-functional-equation.md), for the continuation of $Z(w, s)$ with its only pole, simple with residue $\pi$, at $s = 1$, and for $\Lambda(w, s) = \Lambda(w, 1 - s)$

## Sources

- A. P. Ogg, *On a convolution of L-series*, Invent. Math. 7 (1969), 297–312: §2, p. 303 (the function $\zeta_N$ and the
  computation of $2\zeta_N(2s) F_N(\tau, s)$ as $\sum_{d \mid N} \mu(d) d^{-2s} G(N\tau/d, s)$, with
  $G(\tau, s) = \sum'_{m, n} |m\tau + n|^{-2s}$, so that $\operatorname{Im}(w)^s G(w, s) = Z(w, s)$ and $E_N = y^s F_N$) and p. 304 (the
  function $I(\tau, s) = (y/\pi)^s \Gamma(s) G(\tau, s)$, which is $\Lambda(\tau, s)$).
- W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315: §4, pp. 312–313.
