# Correlated agreement for Reed-Solomon codes on affine spaces (unique-decoding regime)

Let $\mathbb{F}$ be a finite field, $\mathrm{RS}_k \subseteq \mathbb{F}^n$ a Reed-Solomon code at distinct points with $2e + k \le n$, and consider the affine space $u_0 + \sum_{j=1}^{\ell} z_j u_j$, $z \in \mathbb{F}^\ell$. If a set $T \subseteq \mathbb{F}^\ell$ of parameters with every point $e$-close to $\mathrm{RS}_k$ has density

$$\frac{|T|}{|\mathbb{F}|^\ell} > \frac{n}{|\mathbb{F}|}$$

(a threshold independent of $\ell$), then $u_0, u_1, \dots, u_\ell$ have $e$-correlated agreement with $\mathrm{RS}_k$, with a greatest agreement set of size at least $n - e$ and unique agreeing codewords.

## Proof sketch

Some line through the affine space contains more than $n$ points of $T$ by averaging over a fibration by parallel lines; the line theorem gives agreement for that pair of words, and doing this along coordinate directions with the uniqueness of maximal agreement sets glues the pieces into one common agreement set for all $u_j$.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Proof depends on

- [Correlated agreement and proximity gap for Reed-Solomon codes on lines (unique-decoding regime)](reed-solomon-proximity-gap-on-lines-unique-decoding.md)
- [Line-to-affine and affine-to-curve reductions for proximity gaps](line-to-affine-proximity-gap-reductions.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
