# Proximity gaps for Reed-Solomon codes up to the Johnson bound on curves and lines

Let $\mathbb{F}$ be a finite field, $\mathrm{RS}_k \subseteq \mathbb{F}^n$ a Reed-Solomon code at distinct points with $1 \le k \le n$ and rate $\rho = k/n$, and let $\eta > 0$ and an integer $e$ satisfy $e/n \le 1 - \sqrt{\rho} - \eta$. For every $u_0, \dots, u_r \in \mathbb{F}^n$, either every curve point $\sum_{j=0}^{r} z^j u_j$ is within distance $e$ of $\mathrm{RS}_k$, or the fraction of scalars $z \in \mathbb{F}$ for which it is satisfies

$$\frac{|\{z\}|}{|\mathbb{F}|} \le \frac{115200\, r\, n^2}{\rho\, \eta^6\, |\mathbb{F}|}.$$

Above that threshold the words $u_0, \dots, u_r$ have $e$-correlated agreement with $\mathrm{RS}_k$; the line case $r = 1$ also holds with a multiplicity parameter $m$, radius $e/n \le 1 - \sqrt{\rho} - \sqrt{\rho}/(2m)$ and bound $1800 (m + 1)^6 n^2/(\rho |\mathbb{F}|)$. These are explicit-constant forms in the setting of the Ben-Sasson-Carmon-Ishai-Kopparty-Saraf theorem.

## Proof sketch

Run a Guruswami-Sudan interpolation with multiplicity $m$ over the field of rational functions in $Z$: a trivariate polynomial $Q(X, Y, Z)$ vanishes to order $m$ at the points $(\alpha_i, (\sum_j Z^j u_j)_i)$. For each good $z$ the nearby codeword is a root in $Y$; by pigeonhole many good $z$ share an irreducible factor, which after a separable contraction and a good shift has a power-series root lifted by a Taylor recurrence. A resultant argument shows this root is a polynomial in $Z$ of degree at most $r$, and weighted double counting over the good $z$ yields the common agreement set.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)
- [q-ary Johnson radius](../list-decoding/johnson-radius.md)

## Proof depends on

- [Guruswami–Sudan list decoding](../list-decoding/exists-interpolant-dvd.md)
- [Correlated agreement and proximity gap for Reed-Solomon codes on parameterized curves (unique-decoding regime)](reed-solomon-proximity-gap-on-curves-unique-decoding.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
- V. Guruswami, M. Sudan, "Improved Decoding of Reed-Solomon and Algebraic-Geometry Codes", IEEE Transactions on Information Theory, 1999.
