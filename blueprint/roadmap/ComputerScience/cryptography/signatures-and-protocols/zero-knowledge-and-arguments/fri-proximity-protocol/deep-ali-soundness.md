# DEEP quotienting of Reed–Solomon words

Let $f$ be a word on $D$ claimed to be a Reed–Solomon codeword of dimension $k$. For an out-of-domain point $z \in \mathbb{F} \setminus D$ and a claimed value $v$, the *DEEP quotient* is $\mathrm{quot}(f; z, v)(x) = (f(x) - v)/(x - z)$. If $f$ is $\delta$-close to the codeword $p$ with $\delta$ in the unique-decoding radius, then $\mathrm{quot}(f; z, v)$ is $\delta$-close to $\mathrm{RS}$ of dimension $k - 1$ if and only if $v = p(z)$ (for $z \notin D$); and for every $\delta$, if $\mathrm{quot}(f; z, v)$ is $\delta$-close to $\mathrm{RS}$ of dimension $k - 1$, then $v = u(z)$ for some codeword $u$ of dimension $k$ within distance $\delta$ of $f$. The DEEP-ALI protocol applies this quotient, at a random out-of-domain point, to the composition polynomial of an algebraic constraint system and runs FRI on the result.

## Proof sketch

If the quotient agrees with $h \in \mathrm{RS}[k - 1]$ on a set $S$, then $f$ agrees on $S$ with $u = v + (x - z)h$, a codeword of dimension $k$ with $u(z) = v$; this is the general clause. Conversely, if $v = p(z)$, the quotient agrees with $(p - v)/(x - z) \in \mathrm{RS}[k - 1]$ wherever $f$ agrees with $p$. In the unique-decoding radius, $u$ and $p$ are both $\delta$-close to $f$, so $u = p$ and $v = p(z)$.

## Depends on

- [Reed–Solomon folding over multiplicative cosets](reed-solomon-coset-folding.md)
- [Public-coin interactive oracle proofs](../interactive-oracle-proofs/public-coin-iop.md)

## Proof depends on

- [Proximity gaps and correlated agreement for Reed–Solomon codes](reed-solomon-proximity-gaps.md)

## Sources

- Eli Ben-Sasson, Lior Goldberg, Swastik Kopparty and Shubhangi Saraf, "DEEP-FRI: Sampling Outside the Box Improves Soundness", 11th Innovations in Theoretical Computer Science Conference (ITCS 2020), 2020.
