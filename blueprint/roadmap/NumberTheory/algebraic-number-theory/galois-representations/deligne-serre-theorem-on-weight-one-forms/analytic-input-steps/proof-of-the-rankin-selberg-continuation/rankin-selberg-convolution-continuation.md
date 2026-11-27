# Rankin's theorem on the convolution of two cusp forms on Γ₀(N)

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with $\varepsilon(-1) = (-1)^k$, and let
$f = \sum_{n \ge 1} a_n q^n$ and $g = \sum_{n \ge 1} b_n q^n$ be cusp forms of [type $(k, \varepsilon)$ on $\Gamma_0(N)$](../../modular-forms-of-type-k-epsilon.md). Let
$\zeta_N(s) = \prod_{p \nmid N} (1 - p^{-s})^{-1}$, and let

$$\langle f, g \rangle = \int_D f(z)\, \overline{g(z)}\, y^k\, \frac{dx\, dy}{y^2}$$

for a fundamental domain $D$ of $\Gamma_0(N)$, $z = x + iy$. Then the function

$$L_{f,g}(s) = \zeta_N(2s) \sum_{n \ge 1} a_n \overline{b_n}\, n^{-(s+k-1)},$$

holomorphic for $\operatorname{Re}(s) > 1$, extends to a meromorphic function on $\mathbb{C}$ that is holomorphic except for at
most a simple pole at $s = 1$, where its residue is

$$\frac{2\pi^2 (4\pi)^{k-1} \varphi(N)}{N^2\, (k-1)!}\, \langle f, g \rangle,$$

with $\varphi$ Euler's function; so $L_{f,g}$ is entire exactly when $\langle f, g \rangle = 0$. More precisely, with
$\Lambda(w, s) = \pi^{-s} \Gamma(s) Z(w, s)$ the completed Epstein zeta function,

$$\left(\frac{2\pi}{\sqrt{N}}\right)^{-2s} \Gamma(s)\, \Gamma(s + k - 1)\, L_{f,g}(s) = \frac{(4\pi)^{k-1}}{2} \sum_{d \mid N} \mu(d)\, d^{-s} \int_D f(z)\, \overline{g(z)}\, y^k\, \Lambda(Nz/d, s)\, \frac{dx\, dy}{y^2},$$

where each integral is a meromorphic function of $s$ whose only possible poles are simple poles at $s = 1$ and $s = 0$,
with residues $\langle f, g \rangle$ and $-\langle f, g \rangle$.

This is Rankin's theorem as Ogg states it for $\varepsilon = 1$ (Theorem 3, from his formula (4′)) and as Li recalls it
(§4). The displayed identity comes from multiplying the [unfolding identity](rankin-unfolding-identity.md) by
$2\pi^{-s}\Gamma(s)\zeta_N(2s)$ and substituting the expression of $\zeta_N(2s) E_N(z, s)$
[through Epstein zeta functions](eisenstein-series-of-gamma0-via-epstein-zeta.md). The residues of $\Lambda(w, s)$, $1$ at
$s = 1$ and $-1$ at $s = 0$, do not depend on $w$, which gives the residues of the integrals and, with
$\sum_{d \mid N} \mu(d)/d = \varphi(N)/N$, the residue of $L_{f,g}$ at $s = 1$. Since $1/(\Gamma(s)\Gamma(s+k-1))$ is entire and
vanishes at $s = 0$, $L_{f,g}$ has no other pole. The argument uses only that $f(z)\overline{g(z)} y^k$ is invariant under
$\Gamma_0(N)$, which holds for every $\varepsilon$. For $g = f \ne 0$, $\langle f, f \rangle > 0$, so the pole is there and its
residue is positive.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](../../modular-forms-of-type-k-epsilon.md), for cusp forms of type $(k, \varepsilon)$
- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the cusp forms of weight $k$ on $\Gamma_1(N)$
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Functional equation of the Epstein zeta function of a binary form](../../../../../modular-forms-q-series/modular-forms/epstein-zeta-binary-functional-equation.md), for $Z(w, s)$ and $\Lambda(w, s)$

## Proof depends on

- [Rankin's unfolding identity on Γ₀(N)](rankin-unfolding-identity.md), for the integral of $f \overline{g} y^k E_N(z, s)$ on $\operatorname{Re}(s) > 1$
- [The Eisenstein series of Γ₀(N) at the cusp ∞ through Epstein zeta functions](eisenstein-series-of-gamma0-via-epstein-zeta.md), for $2\pi^{-s}\Gamma(s)\zeta_N(2s)E_N(z, s)$ in terms of the $\Lambda(Nz/d, s)$
- [Functional equation of the Epstein zeta function of a binary form](../../../../../modular-forms-q-series/modular-forms/epstein-zeta-binary-functional-equation.md), for the poles of $\Lambda(w, s)$ at $s = 1$ and $s = 0$, of residues $1$ and $-1$

## Expansion

This node is still to be broken down. A good expansion states and links:

- a bound for $\Lambda(w, s) - \frac{1}{s - 1} + \frac{1}{s}$ on $\operatorname{Im}(w) \ge \sqrt{3}/2$, polynomial in
  $\operatorname{Im}(w)$ uniformly for $s$ in compact subsets of $\mathbb{C}$, from the theta integral that continues $\Lambda$;
- the invariance $\Lambda(\gamma w, s) = \Lambda(w, s)$ for $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ (Ogg, p. 304), which with that
  bound controls $\Lambda(Nz/d, s)$ near each cusp of $\Gamma_0(N)$;
- the exponential decay of $f(z) \overline{g(z)} y^k$ at every cusp of $\Gamma_0(N)$, so that each integral converges
  absolutely, locally uniformly in $s$ away from $0$ and $1$, and defines a meromorphic function with the poles stated.

## Sources

- A. P. Ogg, *On a convolution of L-series*, Invent. Math. 7 (1969), 297–312: §2, p. 303 (formulas (3) and (4)) and
  p. 304 (the function $I(\tau, s)$, its poles and its invariance under $\Gamma$, formula (4′), and Theorem 3 (Rankin));
  §1, p. 299, for the Petersson inner product.
- W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315: §4, pp. 312–313.
- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Démonstration 5.2, pp. 518–519, which quotes the
  continuation from Rankin [18], citing also Li [12], Miyake [13] and Ogg [15].
