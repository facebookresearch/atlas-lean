# Gross–Zagier–Zhang formula: when the Heegner point has infinite order

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, let $f$ be its newform, and let
$\psi \colon X_0(N) \to E$ be a
[modular parametrization](../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md)
taking $\infty$ to $O$ of minimal degree among those: such parametrizations exist and their degrees are positive
integers. Let $\omega$ be the minimal invariant differential of $E$, with $\psi^*(\omega) = \alpha \, \omega_f$ for a
nonzero integer $\alpha$, where $\omega_f = 2\pi i f(z)\,dz$, and let $c = \lvert \alpha \rvert$ be the Manin
constant. Let $K$ be an imaginary quadratic field of discriminant $D_K \ne -3, -4$ in which every prime factor of $N$
splits, with no condition on the parity of $D_K$, and let $y_K \in E(K)$ be
[the Heegner point](heegner-point-of-an-elliptic-curve.md) built with $\psi$.

Let $\varepsilon_K$ be the
[quadratic Dirichlet character](../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md)
of $D_K$ and $L(E/K, s) = L(E, s) \, L(E, \varepsilon_K, s)$ the $L$-function of $E$ over $K$, where
$L(E, \varepsilon_K, s) = \sum_{n \ge 1} \varepsilon_K(n) a_n n^{-s}$ for $L(E, s) = \sum_{n \ge 1} a_n n^{-s}$. Then

$$L'(E/K, 1) = \frac{2 \lVert\omega\rVert^2 \, \hat h(y_K)}{c^2 \, \lvert D_K \rvert^{1/2}}, \qquad
\lVert\omega\rVert^2 = \int_{E(\mathbb{C})} \omega \wedge \overline{i\omega},$$

where $\hat h$ is the absolute Néron–Tate height on $E(K)$, normalised by
$\hat h(P) = \frac{1}{2[K : \mathbb{Q}]} \lim_{n \to \infty} 4^{-n} \log H_K(x(2^n P))$ with
$H_K(x) = \prod_v \lvert x \rvert_v^{[K_v : \mathbb{Q}_v]}$ over the places $v$ of $K$; like the
[Néron–Tate height](../../AlgebraicGeometry/not-yet-classified/abelian-arithmetic-heights/neron-tate-height.md), it
vanishes on $E(K)$ exactly at the torsion points. In particular, $y_K$ has infinite order in $E(K)$ if and only if
$L'(E/K, 1) \ne 0$.

Miller states the formula for every imaginary quadratic field in which the prime factors of $N$ split, with a factor
$u_K^2$ in the denominator, where $2u_K$ is the number of roots of unity of $K$; this page is the case
$D_K \ne -3, -4$, where $u_K = 1$, which covers the fields of the Heegner point page.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the [Gross–Zagier formula](gross-zagier-formula.md) for odd $D_K$, with the comparison of normalisations: the
  height of Gross and Zagier, taken over $K$, is twice the absolute height above (Miller, p. 336);
- Zhang's extension of the Gross–Zagier formula, which removes the parity condition on $D_K$;
- the existence of a parametrization of minimal degree, from the existence of one and the positivity of degrees, and
  the integrality of $\alpha$ (Miller cites Edixhoven).

## Depends on

- [The Heegner point of an elliptic curve over an imaginary quadratic field](heegner-point-of-an-elliptic-curve.md), for $y_K$
- [Modular parametrization of an elliptic curve over $\mathbb{Q}$](../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md), for $\psi$, $f$ and $\alpha$
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](../zeta-l-functions/functional-equation-of-the-l-function-of-an-elliptic-curve.md), for the continuation of $L(E, s)$
- [Quadratic Dirichlet character of a fundamental discriminant](../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md), for $\varepsilon_K$
- [The Néron–Tate height of an abelian variety over a number field](../../AlgebraicGeometry/not-yet-classified/abelian-arithmetic-heights/neron-tate-height.md), for the canonical height of $E$ over $K$

## Proof depends on

- [Gross–Zagier formula for the Heegner point](gross-zagier-formula.md), the case of odd $D_K$

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank zero
  and one*, LMS J. Comput. Math. 14 (2011), 327–350, doi:10.1112/S1461157011000180: §4, pp. 335–336, the definition
  of the Heegner hypothesis for $K = \mathbb{Q}(\sqrt{D})$, $D < 0$ squarefree, of the parametrization $\psi$ "of
  minimal degree taking $\infty$ to $O$", of the Manin constant $c$ and of $y_K := \operatorname{Tr}_{H/K}(\psi(x_1))$;
  Theorem 4.1 (Gross–Zagier–Zhang), pp. 335–336 ("If $K$ satisfies the Heegner hypothesis for $E$, then
  $L'(E/K, 1) = \frac{2\lVert\omega\rVert^2 \hat h(y_K)}{c^2 \cdot u_K^2 \cdot \sqrt{\lvert\Delta(K)\rvert}}$, where
  $\lVert\omega\rVert^2 = \int_{E(\mathbb{C})} \omega \wedge \overline{i\omega}$ and the quadratic imaginary number field
  $K$ has $2u_K$ roots of unity and discriminant $\Delta(K)$."), its proof ("Gross and Zagier first proved this in [29]
  when $D$ is odd and Zhang generalized it in [62].") and the paragraph after it, p. 336, on $u_K$ and on the
  normalisation of $\hat h$.
- S.-W. Zhang, *Gross–Zagier formula for $\mathrm{GL}(2)$ II*, in *Heegner points and Rankin $L$-series*, Math. Sci.
  Res. Inst. Publ. 49, Cambridge Univ. Press, 2004, 191–214. Not read here; cited as Miller cites it (p. 336 and his
  reference [62]).
- B. Edixhoven, *On the Manin constants of modular elliptic curves*, in *Arithmetic algebraic geometry* (Texel, 1989),
  Birkhäuser, 1991, 25–39. Not read here; cited as Miller cites it (p. 335 and his reference [21]).
