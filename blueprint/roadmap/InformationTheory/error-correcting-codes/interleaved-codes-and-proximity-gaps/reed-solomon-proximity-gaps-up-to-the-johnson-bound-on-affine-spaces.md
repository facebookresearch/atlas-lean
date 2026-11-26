# Proximity gaps for Reed-Solomon codes up to the Johnson bound on affine spaces

Let $\mathbb{F}$ be a finite field, $\mathrm{RS}_k \subseteq \mathbb{F}^n$ a Reed-Solomon code at distinct points with rate $\rho = k/n$, $1 \le k \le n$, and let $\eta > 0$ and $e$ satisfy $e/n \le 1 - \sqrt{\rho} - \eta$. For every affine space $u_0 + \sum_{j=1}^{\ell} z_j u_j$, either every point is within distance $e$ of $\mathrm{RS}_k$ or the fraction of parameters $z \in \mathbb{F}^\ell$ whose point is $e$-close is at most

$$\frac{115200\, n^2}{\rho\, \eta^6\, |\mathbb{F}|},$$

independently of $\ell$; above this density the generators have $e$-correlated agreement with $\mathrm{RS}_k$. Weighted versions, in which agreement is measured by nonnegative integer or rational coordinate weights, hold with the same structure.

## Proof sketch

Reduce the affine space to curves by the fibre-averaging reduction and apply the Johnson-regime curve theorem; the dichotomy follows from correlated agreement exactly as in the unique-decoding case. Rational weights are cleared to integer weights by a common denominator.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)
- [q-ary Johnson radius](../list-decoding/johnson-radius.md)

## Proof depends on

- [Proximity gaps for Reed-Solomon codes up to the Johnson bound on curves and lines](reed-solomon-proximity-gaps-up-to-the-johnson-bound-on-curves.md)
- [Line-to-affine and affine-to-curve reductions for proximity gaps](line-to-affine-proximity-gap-reductions.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
