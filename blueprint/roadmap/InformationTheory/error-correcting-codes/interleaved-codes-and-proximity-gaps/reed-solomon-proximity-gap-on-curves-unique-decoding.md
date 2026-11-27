# Correlated agreement and proximity gap for Reed-Solomon codes on parameterized curves (unique-decoding regime)

Let $\mathrm{RS}_k \subseteq \mathbb{F}^n$ be a Reed-Solomon code at distinct points, $2e + k \le n$, and $u_0, \dots, u_d \in \mathbb{F}^n$. If more than $d n$ scalars $z \in \mathbb{F}$ make the curve point $\sum_{j=0}^{d} z^j u_j$ lie within Hamming distance $e$ of $\mathrm{RS}_k$, then $u_0, \dots, u_d$ have $e$-correlated agreement with $\mathrm{RS}_k$, with a greatest agreement set of size at least $n - e$ and unique agreeing codewords. Over a finite field, for every $u_0, \dots, u_d$ either every curve point is $e$-close to $\mathrm{RS}_k$ or at most $d n$ scalars are.

## Proof sketch

As for lines, the Berlekamp-Welch identities for good $z$ assemble into a bivariate identity whose degree in $z$ is now at most $d$ times larger, so more than $dn$ good scalars make it an identity and expose a shared error locator. The converse direction and uniqueness are as in the line case.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Proof depends on

- [Correlated agreement and proximity gap for Reed-Solomon codes on lines (unique-decoding regime)](reed-solomon-proximity-gap-on-lines-unique-decoding.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
