# Gross–Zagier formula for the Heegner point

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, let $f$ be its
newform and $\varphi \colon X_0(N) \to E$ a
[modular parametrization](../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md)
with $\varphi(\infty) = O$, and let $\omega$ be the Néron differential of $E$ with $\varphi^*(\omega) = c\,\omega_f$,
$c > 0$, where $\omega_f = 2\pi i f(z)\,dz$. Let $K$ be an imaginary quadratic field as for
[the Heegner point](heegner-point-of-an-elliptic-curve.md): its discriminant $D_K$ is not $-3$ or $-4$ and every prime
factor of $N$ splits in $K$. Assume moreover that $D_K$ is odd. (For $D_K$ prime to $N$, the splitting condition is
Gross and Zagier's condition that $D_K$ be a square modulo $4N$.) Let $y_K \in E(K)$ be the Heegner point.

Let $\varepsilon_K$ be the
[quadratic Dirichlet character](../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md)
of $D_K$ and
$L(E/K, s) = L(E, s) \, L(E, \varepsilon_K, s)$ the $L$-function of $E$ over $K$, where
$L(E, \varepsilon_K, s) = \sum_{n \ge 1} \varepsilon_K(n) a_n n^{-s}$ for $L(E, s) = \sum_{n \ge 1} a_n n^{-s}$; it
extends to an entire function and vanishes at $s = 1$. Then

$$L'(E/K, 1) = \frac{\lVert\omega\rVert^2 \, \hat h(y_K)}{c^2 \, \lvert D_K \rvert^{1/2}}, \qquad
\lVert\omega\rVert^2 = \iint_{E(\mathbb{C})} \lvert \omega \wedge \bar\omega \rvert,$$

where $\hat h$ is the canonical height of $E$ over $K$, normalised as by Gross and Zagier (Chapter I, §4, and (6.4)),
$\hat h(P) = \lim_{n \to \infty} 4^{-n} \log H_K(x(2^n P))$ with $H_K(x) = \prod_v \max(1, \lvert x \rvert_v)^{[K_v : \mathbb{Q}_v]}$
over the places $v$ of $K$, where $x(O) = \infty$ and $H_K(\infty) = 1$, the height of the point $(0 : 1)$, so that
$\hat h(O) = 0$ (the height over $K$, as Coates defines it with the coordinates $(1 : x)$; twice the absolute height
$\lim_{n \to \infty} 4^{-n} h(x(2^n P))$ of the [Gross–Zagier–Zhang page](gross-zagier-zhang-formula.md)): a
positive definite quadratic form on $E(K) \otimes \mathbb{R}$, so that, like the
[Néron–Tate height](../../AlgebraicGeometry/not-yet-classified/abelian-arithmetic-heights/neron-tate-height.md), it
vanishes on $E(K)$ exactly at the torsion points. In particular, $y_K$ has infinite order in $E(K)$ if and only if
$L'(E/K, 1) \ne 0$.

## Expansion

This node is still to be broken down. A good expansion states and links, following the plan of Gross and Zagier
(Chapter I, §9):

- Rankin's method for the continuation and functional equation of $L(f, \chi, s)$ and its vanishing at $s = 1$
  (Chapter I, Proposition (5.5); Chapter IV), and the cusp form $\Phi_{\mathcal{A}}$ of Chapter I, (9.2), a holomorphic
  projection of a Rankin product, determined by (9.2) up to the addition of an oldform;
- the decomposition of the height pairing of Heegner divisors on the Jacobian of $X_0(N)$ into local heights, computed
  at the archimedean places with Green's functions (Chapter II) and at the finite places by intersection theory on a
  model of $X_0(N)$ (Chapter III);
- the comparison of Fourier coefficients for the indices prime to the level, $\langle c, T_m c^\sigma \rangle =
  u^2 a_{m, \mathcal{A}}$ for $m \ge 1$ with $(m, N) = 1$ (Chapter I, (9.3); Chapter V, §1), by which the cusp form
  $g_{\mathcal{A}} = \sum_{m \ge 1} \langle c, T_m c^\sigma \rangle q^m$ and $u^2 \Phi_{\mathcal{A}}$ differ by an
  oldform, so have the same Petersson product with every newform of weight $2$ and level $N$: this, and not an equality
  of the two forms, is Theorem (6.1) of Chapter I, from which Theorem (6.3) follows by the formalism of Chapter V, §1;
- the passage from the Jacobian to $E$ in Chapter V, §2, with $\hat h(P_K) = \hat h(c_{\mathbf{1}, f}) \deg(\pi)$
  and $\lVert\omega\rVert^2 = c^2 \lVert\omega_f\rVert^2 / \deg(\pi)$.

Gross and Zagier assume throughout that the discriminant is odd (Chapter I, §3, p. 227). The
[Gross–Zagier–Zhang formula](gross-zagier-zhang-formula.md) states the result without that assumption.

## Depends on

- [Quadratic Dirichlet character of a fundamental discriminant](../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md), for $\varepsilon_K$
- [The Heegner point of an elliptic curve over an imaginary quadratic field](heegner-point-of-an-elliptic-curve.md), for $y_K$
- [Modular parametrization of an elliptic curve over $\mathbb{Q}$](../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md), for $\varphi$, $f$ and the constant $c$
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](../zeta-l-functions/functional-equation-of-the-l-function-of-an-elliptic-curve.md), for the continuation of $L(E, s)$
- [The Néron–Tate height of an abelian variety over a number field](../../AlgebraicGeometry/not-yet-classified/abelian-arithmetic-heights/neron-tate-height.md), for the canonical height of $E$ over $K$

## Proof depends on

- [Decomposition of rational primes in a quadratic field](../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md), for the comparison of the splitting condition with Gross and Zagier's: for $D_K$ prime to $N$, a prime $\ell \mid N$ splits in $K$ exactly when $\left(\frac{D_K}{\ell}\right) = 1$, from which, with Hensel's lemma, $D_K$ is a square modulo $4N$
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../modular-forms-q-series/modular-forms/hecke-endomorphisms-of-the-modular-jacobian.md), for the Hecke correspondences $T_m$ acting on $J_0(N)$ in the pairings $\langle c, T_m c^\sigma \rangle$
- [The Heegner point of an elliptic curve over an imaginary quadratic field](heegner-point-of-an-elliptic-curve.md), for the rationality of the Heegner points over the Hilbert class field

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320:
  Chapter V, §2, Theorem (2.1), p. 311 ("$L'(E/K, 1) = \lVert\omega\rVert^2 \hat h(P_K)/c^2 u_K^2 \lvert D\rvert^{\frac12}$"),
  with the notation of p. 310 ($\pi$, $\omega$, $c$, $P_K$ and "$\lVert\omega\rVert^2 \underset{\text{def}}{=} \iint_{E(\mathbb{C})} \lvert\omega \wedge \bar\omega\rvert$",
  the heights taken over $K$); here $u_K = 1$ as $D_K \ne -3, -4$. Chapter I: §3, p. 227 (Heegner points; the
  standing assumption that $D$ is odd); §4, p. 228 (the height is positive definite on $J(H) \otimes \mathbb{R}$);
  §5, Proposition (5.5), p. 229; §6, Theorems (6.1) and (6.3), (6.4) and (6.5), p. 230; §9, the plan of proof, pp. 232–233, with (9.2) and (9.3),
  p. 233.
  Chapter V, §1, p. 307 ("this means that $g_{\mathcal{A}}$ and $u^2 \sum a_{m,\mathcal{A}} q^m$ differ by an old form in
  $S_2(\Gamma_0(N))$, so they have the same Petersson scalar product with any $f$ in the space spanned by newforms of
  weight 2 and level $N$, which is just assertion of Theorem (6.1) of Chap. I.").
- J. Coates, *The work of Gross and Zagier on Heegner points and the derivatives of $L$-series*, Séminaire Bourbaki,
  exp. 635 (1984/85), Astérisque 133–134 (1986), 57–72, <http://www.numdam.org/item?id=SB_1984-1985__27__57_0>:
  Theorem 4, p. 64, and (7), p. 65 ("$L(E/K, s) = L(E, s)\,L(E^{(\varepsilon)}, s) = L(f, \chi_0, s)$"); pp. 60–61, the
  canonical height on the Jacobian over a number field $F$ as a limit of $n^{-2} \sum_{v \in M_F} \max_i \log \lvert x_i(nP) \rvert_v$,
  with $\lvert\cdot\rvert_v$ normalised by the local degree, and p. 65, the analogous height on $E$ through the
  $x$-coordinate.
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: (1.1), p. 235, and "In particular,
  the point $y_K$ has infinite order if and only if $L'(E/K, 1) \neq 0$."
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Theorem 3.20 (1), p. 40, stated up to a nonzero factor, and (3.12), p. 37.
