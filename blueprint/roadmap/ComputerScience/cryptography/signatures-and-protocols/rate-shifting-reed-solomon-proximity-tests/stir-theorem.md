# STIR: Reed–Solomon proximity testing with O(log d + λ·log log d) queries

Let $\lambda$ be a security parameter and $\mathrm{RS}[\mathbb{F},L,d]$ a Reed–Solomon code of rate $\rho = d/|L|$, with $d$ a power of $2$ and $L$ a smooth domain (a multiplicative coset of $\mathbb{F}^*$ whose size is a power of $2$). Let $\delta \in (0, 1 - 1.05\sqrt{\rho})$ be a proximity parameter and $k \ge 4$ a folding parameter that is a power of $2$. If $|\mathbb{F}| = \Omega(\lambda\cdot 2^{\lambda}\cdot d^{3}\cdot|L|^{3.5}/\log(1/\rho))$, there is a public-coin IOPP for $\mathrm{RS}[\mathbb{F},L,d]$ with proximity parameter $\delta$ and round-by-round soundness error $2^{-\lambda}$ that makes $\lambda/(-\log(1-\delta))$ queries to the input and, for fixed $k$, has round complexity $O(\log d)$ and makes $O(\log d+\lambda\cdot\log(\log d/\log(1/\rho)))$ queries to the proof strings. In particular, for constant $\rho$, $\delta$ and $k$ its query complexity is $O(\log d+\lambda\cdot\log\log d)$, compared with $O(\lambda\cdot\log d/\log(1/\rho))$ for FRI. Compiled with the BCS transformation, which applies because round-by-round soundness implies state-restoration soundness, it yields a SNARG in the random oracle model in which each IOPP query costs one Merkle-tree opening.

## Proof sketch

Each iteration improves the rate geometrically while reducing degree by $k$, so the number of queries needed per round to achieve $\lambda$ bits of soundness, about $\lambda/\log(1/\rho_i)$, decreases geometrically. Summing over $O(\log_k d)$ rounds gives the proof-string query bound. Round-by-round soundness follows from the iteration lemma, whose analysis in the list-decoding regime uses the Johnson bound, and makes the BCS compilation sound in the random oracle model.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)
- [Merkle root](../../hash-functions/merkle-trees/root.md)

## Proof depends on

- [One STIR iteration: fold, shift to a smaller domain, quotient](stir-iteration.md)
- [Johnson-bound list size for Reed–Solomon codes](johnson-list-size.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390 (Theorem 1 and Theorem 5.1).
- Eli Ben-Sasson, Alessandro Chiesa, Nicholas Spooner, "Interactive Oracle Proofs", TCC (2016).
