# Proximity gaps for Reed-Solomon codes up to the Johnson bound on affine spaces

Let $\mathbb{F}$ be a finite field, $\mathrm{RS}_k \subseteq \mathbb{F}^n$ a Reed-Solomon code at distinct points with rate $\rho = k/n$, $1 \le k \le n$, and let $\eta > 0$ and $e$ satisfy $e/n \le 1 - \sqrt{\rho} - \eta$. For every affine space $u_0 + \sum_{j=1}^{\ell} z_j u_j$, either every point is within distance $e$ of $\mathrm{RS}_k$ or the fraction of parameters $z \in \mathbb{F}^\ell$ whose point is $e$-close is at most

$$\frac{\rho^2 n^2}{\big(2\min(\eta, \sqrt{\rho}/20)\big)^7\, |\mathbb{F}|},$$

independently of $\ell$; above this density the generators have $e$-correlated agreement with $\mathrm{RS}_k$ (Ben-Sasson, Carmon, Ishai, Kopparty and Saraf, Theorems 1.2 and 1.6).

## Proof sketch

Reduce the affine space to curves by the fibre-averaging reduction and apply the Johnson-regime curve theorem; the dichotomy follows from correlated agreement exactly as in the unique-decoding case.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)
- [q-ary Johnson radius](../list-decoding/johnson-radius.md)

## Proof depends on

- [Proximity gaps for Reed-Solomon codes up to the Johnson bound on curves and lines](reed-solomon-proximity-gaps-up-to-the-johnson-bound-on-curves.md)
- [Line-to-affine and affine-to-curve reductions for proximity gaps](line-to-affine-proximity-gap-reductions.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023, Theorems 1.2 and 1.6.
