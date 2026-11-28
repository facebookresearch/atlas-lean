# Correlated agreement and proximity gap for Reed-Solomon codes on parameterized curves (unique-decoding regime)

Let $\mathbb{F}_q$ be a finite field, $\mathrm{RS}_k \subseteq \mathbb{F}_q^n$ the Reed-Solomon code of polynomials of degree less than $k$ at distinct points of $\mathbb{F}_q$, $2e + k \le n$, and $u_0, \dots, u_d \in \mathbb{F}_q^n$. If more than $d n$ scalars $z \in \mathbb{F}_q$ make the curve point $\sum_{j=0}^{d} z^j u_j$ lie within Hamming distance $e$ of $\mathrm{RS}_k$, then every curve point does, and $u_0, \dots, u_d$ have $e$-correlated agreement with $\mathrm{RS}_k$. If moreover $e \ge 1$, there is a unique maximal agreement set, of size at least $n - e$, with unique agreeing codewords. Consequently, for every $u_0, \dots, u_d$ either every curve point is $e$-close to $\mathrm{RS}_k$ or at most $d n$ scalars are.

## Proof sketch

As for lines, the Berlekamp-Welch identities for good $z$ assemble into a bivariate identity whose degree in $z$ is now at most $d$ times larger, so more than $dn$ good scalars make it an identity and expose a shared error locator. Uniqueness is as in the line case; for $e = 0$ the only agreement set is the whole index set.

In the source the code has degree at most $k'$, rate $\rho = (k' + 1)/n$ and proximity $\delta = e/n \le (1 - \rho)/2$, which is $2e + k \le n$ for $k = k' + 1$, and the curve hypothesis reads $\Pr_z[\cdot] > d \cdot \varepsilon_U$ with $\varepsilon_U = n/q$, that is, more than $dn$ good scalars.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Proof depends on

- [Correlated agreement and proximity gap for Reed-Solomon codes on lines (unique-decoding regime)](reed-solomon-proximity-gap-on-lines-unique-decoding.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023, Section 6, Theorem 6.1, and the unique-decoding clause of Theorem 1.5.
