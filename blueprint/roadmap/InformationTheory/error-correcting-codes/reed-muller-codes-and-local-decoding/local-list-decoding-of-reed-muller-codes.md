# Local list decoding of Reed-Muller codes along lines with advice

Let $\mathbb{F}$ have $q$ elements, $Q = q^m$, and let $p$ be a polynomial of total degree at most $d \ge 1$ on $\mathbb{F}^m$ that agrees with a received word $g$ on $a$ points, with $\mu = q a / Q$ the expected number of agreements on a line. Let $D < q$ be such that more than $q$ monomials $X^i Y^j$ have $(1, d)$-weighted degree $i + d j \le D$, and suppose $D < \mu$. The decoder on input $x$ restricts $g$ to the line through $x$ and an advice point $z$, runs Sudan's list decoder there, and selects the candidate whose value at $z$ equals the advice $p(z)$. Then for some $z$, this decoder computes $p(x)$ correctly at all but at most

$$1 + \frac{1}{Q}\Bigl(\frac{q\, a\, (Q - 1)}{(\mu - D)^2} + \frac{Q(Q - 1)(D - d)}{q - 1}\Bigr)$$

points $x$. The selected candidate's value at the decoding point can be computed from the interpolant by Newton (Hensel) iteration without root finding whenever the root is simple.

## Proof sketch

A line through $x$ and $z$ contains $q$ points of which a pairwise-independent number agree with $p$; Chebyshev's inequality bounds the lines with fewer than $D$ agreements by the first term. On good lines Sudan's interpolant $Q$ is divisible by $Y - p|_{\text{line}}$, and the cofactor vanishes at the advice point only for at most $D - d$ parameters, which gives the second term after averaging over $z$. When the root is simple, $\partial Q/\partial Y \ne 0$ there, so Newton iteration lifts the advice value to the whole line.

## Depends on

- [Minimum distance of q-ary Reed-Muller codes](minimum-distance-of-q-ary-reed-muller-codes.md)
- [Weighted degree bound](../list-decoding/weighted-deg-le.md)

## Proof depends on

- [Guruswami–Sudan list decoding](../list-decoding/exists-interpolant-dvd.md)
- [Reed–Solomon codes are list decodable up to the Johnson radius](../list-decoding/card-le-of-agree-ge.md)

## Sources

- M. Sudan, L. Trevisan, S. Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and System Sciences, 2001.
- M. Sudan, "Decoding of Reed Solomon Codes beyond the Error-Correction Bound", Journal of Complexity, 1997.
- V. Guruswami, M. Sudan, "Improved Decoding of Reed-Solomon and Algebraic-Geometry Codes", IEEE Transactions on Information Theory, 1999.
