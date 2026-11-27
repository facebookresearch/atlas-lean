# Correlated agreement and proximity gap for Reed-Solomon codes on lines (unique-decoding regime)

Let $\alpha_1, \dots, \alpha_n$ be distinct elements of a field $\mathbb{F}$, $\mathrm{RS}_k$ the Reed-Solomon code of polynomials of degree less than $k$ evaluated there, and $2e + k \le n$. If $u_0, u_1 \in \mathbb{F}^n$ and more than $n$ scalars $z \in \mathbb{F}$ make $u_0 + z u_1$ lie within Hamming distance $e$ of $\mathrm{RS}_k$, then $u_0, u_1$ have $e$-correlated agreement with $\mathrm{RS}_k$; moreover there is a greatest such agreement set $D'$, $|D'| \ge n - e$, and the codewords $v_0, v_1$ agreeing with $u_0, u_1$ on it are unique. Consequently, over a finite field, for every $u_0, u_1$ either every point $u_0 + z u_1$ ($z \in \mathbb{F}$) is $e$-close to $\mathrm{RS}_k$, or at most $n$ scalars are, a fraction at most $n/|\mathbb{F}|$.

## Proof sketch

Use Berlekamp-Welch key equations along the line: for each good $z$ there is an error locator of degree $e$ and a quotient polynomial, and treating $z$ as a variable gives a polynomial identity in $(X, Z)$ of low degree in $Z$. More than $n$ good scalars force the identity to hold for all $z$, which exposes a common error locator, hence a common agreement set. Uniqueness and maximality follow because two agreement witnesses of size at least $n - e$ overlap in at least $k$ points, where Reed-Solomon codewords are determined.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Proof depends on

- [Berlekamp-Welch decoder](../reed-solomon-codes/decode.md)
- [Reed-Solomon codes are MDS](../reed-solomon-codes/min-dist-code.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
