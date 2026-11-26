# Out-of-domain sampling pins down a unique list-decoded codeword

Let $f:L\to\mathbb{F}$ and let $\Lambda$ be the list of codewords of $\mathrm{RS}[\mathbb{F},L,d]$ within relative distance $\delta$ of $f$, with $|\Lambda|\le\ell$. For $z$ uniform in $\mathbb{F}\setminus L$, the probability that two distinct members of $\Lambda$ agree at $z$ is at most $\binom{\ell}{2}\frac{d-1}{|\mathbb{F}|-|L|}$. Hence, after the prover answers $y=\hat{f}(z)$ for a random out-of-domain $z$, except with that probability at most one codeword in $\Lambda$ is consistent with $(z,y)$, which lets a proximity test operate beyond the unique-decoding radius.

## Proof sketch

Two distinct polynomials of degree $< d$ agree on at most $d-1$ points; take a union bound over the $\binom{\ell}{2}$ pairs.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)

## Proof depends on

- [Johnson-bound list size for Reed–Solomon codes](johnson-list-size.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586.
