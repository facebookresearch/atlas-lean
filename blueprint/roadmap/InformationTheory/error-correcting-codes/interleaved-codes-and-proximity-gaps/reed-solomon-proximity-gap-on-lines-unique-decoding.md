# Correlated agreement and proximity gap for Reed-Solomon codes on lines (unique-decoding regime)

Let $\mathbb{F}_q$ be a finite field, $\alpha_1, \dots, \alpha_n$ distinct elements of $\mathbb{F}_q$, $\mathrm{RS}_k$ the Reed-Solomon code of polynomials of degree less than $k$ evaluated there, and $2e + k \le n$. If $u_0, u_1 \in \mathbb{F}_q^n$ and the set $S$ of scalars $z \in \mathbb{F}_q$ for which $u_0 + z u_1$ lies within Hamming distance $e$ of $\mathrm{RS}_k$ has more than $n$ elements, then $S = \mathbb{F}_q$ and $u_0, u_1$ have $e$-correlated agreement with $\mathrm{RS}_k$: there are codewords $v_0, v_1$ such that $(u_0, u_1)$ and $(v_0, v_1)$ differ in at most $e$ coordinates. If moreover $e \ge 1$, there is a unique maximal agreement set $D'$, $|D'| \ge n - e$, and the codewords $v_0, v_1$ agreeing with $u_0, u_1$ on it are unique. Consequently, for every $u_0, u_1$ either every point $u_0 + z u_1$ ($z \in \mathbb{F}_q$) is $e$-close to $\mathrm{RS}_k$, or at most $n$ scalars are, a fraction at most $n/q$.

## Proof sketch

Use Berlekamp-Welch key equations along the line: for each good $z$ there is an error locator of degree $e$ and a quotient polynomial, and treating $z$ as a variable gives a polynomial identity in $(X, Z)$ of low degree in $Z$. More than $n$ good scalars force the identity to hold for all $z$ (a Polishchuk-Spielman divisibility argument), which exposes a common error locator, hence a common agreement set. Uniqueness and maximality follow because two agreement witnesses of size at least $n - e$ overlap in at least $k$ points, where Reed-Solomon codewords are determined; for $e = 0$ the only agreement set is the whole index set.

The source works with codewords of degree at most $k'$ and rate $\rho = (k' + 1)/n$ and proximity $\delta = e/n \le (1 - \rho)/2$; with $k = k' + 1$ this is $2e + k \le n$. The argument does not use the finiteness of the field, so the first claim plausibly extends to infinite fields; that extension is not stated in the source and is not claimed here.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Proof depends on

- [Berlekamp-Welch decoder](../reed-solomon-codes/decode.md)
- [Reed-Solomon codes are MDS](../reed-solomon-codes/min-dist-code.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023, Section 4, Theorem 4.1 and Remark 4.1, and the unique-decoding clause of Theorem 1.4.
