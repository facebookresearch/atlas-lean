# Complex conjugation on the Heegner point

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, let $K$ be an
imaginary quadratic field of discriminant $D_K \ne -3, -4$ in which every prime factor of $N$ splits, and let
$y_K \in E(K)$ be [the Heegner point](heegner-point-of-an-elliptic-curve.md). Let $\tau$ be complex conjugation, the
nontrivial automorphism of $K$, and let $w(E) \in \{1, -1\}$ be the root number of $E$, the sign in the functional
equation of
[its $L$-function](../zeta-l-functions/functional-equation-of-the-l-function-of-an-elliptic-curve.md). Then

$$\tau(y_K) = -w(E) \, y_K + t \qquad \text{for a torsion point } t \in E(K).$$

In particular, if $w(E) = -1$, then $y_K + \tau(y_K)$ is a point of $E(\mathbb{Q})$ that differs from $2y_K$ by a
torsion point, so $E(\mathbb{Q})$ has a point of infinite order when $y_K$ has infinite order.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the identity $x_n^\tau = w_N(x_n^{\sigma'})$ on $X_0(N)$ for the Heegner points $x_n$ of conductor $n$ and some
  $\sigma' \in \operatorname{Gal}(K_n/K)$, from complex multiplication (Gross cites his *Heegner points on $X_0(N)$*, §5);
- the finiteness of the class of $(0) - (\infty)$ in the Jacobian of $X_0(N)$;
- Gross's Proposition 5.3, which follows from these: $y_n^\tau = \varepsilon \cdot y_n^{\sigma'} + (\text{torsion})$
  in $E(K_n)$, with $\varepsilon$ the eigenvalue of the Fricke involution $w_N$ on the newform of $E$;
- the case $n = 1$: summing over $\operatorname{Gal}(K_1/K)$ and using $\tau \sigma \tau = \sigma^{-1}$ gives
  $\tau(y_K) = \varepsilon y_K + t$, and $\varepsilon = -w(E)$ by item 2 of the functional equation page. This summation
  is worked out here; Darmon states the conclusion, in terms of $\operatorname{sign}(E, \mathbb{Q}) = w(E)$, in the proof
  of his Theorem 3.22.

## Depends on

- [The Heegner point of an elliptic curve over an imaginary quadratic field](heegner-point-of-an-elliptic-curve.md), for $y_K$
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](../zeta-l-functions/functional-equation-of-the-l-function-of-an-elliptic-curve.md), for $w(E)$

## Proof depends on

- [The Heegner point of an elliptic curve over an imaginary quadratic field](heegner-point-of-an-elliptic-curve.md), for $x_1$, $y_1$ and the trace
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](../zeta-l-functions/functional-equation-of-the-l-function-of-an-elliptic-curve.md), for $w(E) = -\varepsilon$ (its item 2)

The rest of its proof is that of the sources below, as the Expansion describes.

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
