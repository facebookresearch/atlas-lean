# Complex conjugation on the Heegner point

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, let $K$ be an
imaginary quadratic field of discriminant $D_K \ne -3, -4$ in which every prime factor of $N$ splits, and let
$y_K \in E(K)$ be [the Heegner point](../heegner-points-on-x0-n/heegner-point-of-an-elliptic-curve.md). Let $\tau$ be complex conjugation, the
nontrivial automorphism of $K$, and let $w(E) \in \{1, -1\}$ be the root number of $E$, the sign in the functional
equation of
[its $L$-function](../../zeta-l-functions/root-number-and-parity/functional-equation-of-the-l-function-of-an-elliptic-curve.md). Then

$$\tau(y_K) = -w(E) \, y_K + t \qquad \text{for a torsion point } t \in E(K).$$

In particular, if $w(E) = -1$, then $y_K + \tau(y_K)$ is a point of $E(\mathbb{Q})$ that differs from $2y_K$ by a
torsion point, so $E(\mathbb{Q})$ has a point of infinite order when $y_K$ has infinite order.

Gross's proof, with $n = 1$: by [complex conjugation on Heegner points](complex-conjugation-on-heegner-points-of-x0-n.md),
$x_1^\tau = w_N(x_1^{\sigma'})$ for some $\sigma' \in \operatorname{Gal}(K_1/K)$; applying the parametrization $\varphi$ and
[the Fricke involution on it](atkin-lehner-involutions-on-a-modular-parametrization.md) (the case $Q = N$),
$y_1^\tau = \varepsilon \, y_1^{\sigma'} + \varphi(0)$, where $\varphi(0)$ has finite order by the
[finiteness of the cuspidal class](cuspidal-divisor-of-x0-n-has-finite-order.md) and
$\varepsilon$ is the Fricke eigenvalue of the newform of $E$. Summing over $\operatorname{Gal}(K_1/K)$ by
[the trace lemma](../heegner-point-construction/smul-sum-smul-eq-of-mul-eq-inv-mul.md) gives
$\tau(y_K) = \varepsilon y_K + t$ with $t$ of finite order, and $\varepsilon = -w(E)$ by item 2 of
[the functional equation](../../zeta-l-functions/root-number-and-parity/functional-equation-of-the-l-function-of-an-elliptic-curve.md). When
$w(E) = -1$, the point $y_K + \tau(y_K) = 2y_K + t$ is fixed by $\operatorname{Gal}(K/\mathbb{Q})$, so lies in $E(\mathbb{Q})$.

## Depends on

- [The Heegner point of an elliptic curve over an imaginary quadratic field](../heegner-points-on-x0-n/heegner-point-of-an-elliptic-curve.md), for $y_K$
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](../../zeta-l-functions/root-number-and-parity/functional-equation-of-the-l-function-of-an-elliptic-curve.md), for $w(E)$

## Proof depends on

- [Complex conjugation on Heegner points of $X_0(N)$](complex-conjugation-on-heegner-points-of-x0-n.md), for $x_1^\tau = w_N(x_1^{\sigma'})$
- [Atkin–Lehner involutions on a modular parametrization](atkin-lehner-involutions-on-a-modular-parametrization.md), for $\varphi(w_N x) = \varepsilon \varphi(x) + \varphi(0)$, its case $Q = N$
- [The cuspidal divisor $(0) - (\infty)$ has finite order](cuspidal-divisor-of-x0-n-has-finite-order.md), for $\varphi(0)$ of finite order
- [Traces under a dihedral action](../heegner-point-construction/smul-sum-smul-eq-of-mul-eq-inv-mul.md), for the passage from $y_1$ to $y_K$
- [The Heegner point of an elliptic curve over an imaginary quadratic field](../heegner-points-on-x0-n/heegner-point-of-an-elliptic-curve.md), for $x_1$, $y_1$ and the trace
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](../../zeta-l-functions/root-number-and-parity/functional-equation-of-the-l-function-of-an-elliptic-curve.md), for $w(E) = -\varepsilon$ (its item 2)

## Sources

- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: (5.2) and Proposition 5.3 with its
  proof, p. 243 ("We have $y_n^\tau = \epsilon \cdot y_n^{\sigma'} +$ (torsion) in $E(K_n)$, for some
  $\sigma' \in \mathcal{G}_n$."); the commutation relation $\tau\sigma = \sigma^{-1}\tau$ in the proof of
  Proposition 5.4, p. 243.
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Proposition 3.11, p. 36 (for a reflection $\tau \in \operatorname{Gal}(H/\mathbb{Q})$,
  $\tau P_n = -\operatorname{sign}(E, \mathbb{Q})\,\sigma P_n \pmod{E(H)_{\mathrm{tors}}}$ for some
  $\sigma \in \operatorname{Gal}(H/K)$; "Proof. See [Gr84]."), and the proof of Theorem 3.22, p. 41 ("By
  Proposition 3.11, $P_K$ belongs to $E(\mathbb{Q})$ (up to torsion) if and only if $\operatorname{sign}(E, \mathbb{Q}) = -1$.").
- B. H. Gross, *Heegner points on $X_0(N)$*, in *Modular forms* (Durham, 1983), Ellis Horwood, Chichester, 1984,
  87–105 (87–106 in Gross's bibliography), §5. Not read here; cited as Gross (1991, p. 243) and Darmon (p. 36) cite it.
