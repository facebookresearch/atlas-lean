# DEEP quotienting and soundness of DEEP-ALI

Let $f$ be a word on $D$ claimed to be a Reed–Solomon codeword of dimension $k$. For an out-of-domain point $z \in \mathbb{F} \setminus D$ and a claimed value $v$, the *DEEP quotient* is $\mathrm{quot}(f; z, v)(x) = (f(x) - v)/(x - z)$. If $f$ is $\delta$-close to the codeword $p$ with $\delta$ in the unique-decoding radius, then $\mathrm{quot}(f; z, v)$ is $\delta$-close to $\mathrm{RS}$ of dimension $k - 1$ if and only if $v = p(z)$ (for $z \notin D$); in the list-decoding regime the same holds for a uniformly random $z$ except with probability at most $L \cdot k/|\mathbb{F}|$, where $L$ is the list size. Combining DEEP quotienting with algebraic linking of constraint polynomials (DEEP-ALI) and FRI on the quotient yields an IOP for algebraic constraint satisfaction whose soundness error is the FRI error plus $O(L k/|\mathbb{F}|)$ terms.

## Proof sketch

$f - v$ vanishes at $z$ exactly when $v = p(z)$, in which case division by $x - z$ maps codewords to codewords of one lower dimension; distinct list elements agree at a random $z$ with probability at most $k/|\mathbb{F}|$.

## Depends on

- [Reed–Solomon folding over multiplicative cosets](reed-solomon-coset-folding.md)
- [Public-coin interactive oracle proofs](../interactive-oracle-proofs/public-coin-iop.md)

## Proof depends on

- [Proximity gaps and correlated agreement for Reed–Solomon codes](reed-solomon-proximity-gaps.md)

## Sources

- Eli Ben-Sasson, Lior Goldberg, Swastik Kopparty and Shubhangi Saraf, "DEEP-FRI: Sampling Outside the Box Improves Soundness", 11th Innovations in Theoretical Computer Science Conference (ITCS 2020), 2020.
