# STIR: Reed–Solomon proximity testing with O(log d + λ·log log d) queries

For every security parameter $\lambda$, degree $d$, and constant rate $\rho$, there is a public-coin IOPP for $\mathrm{RS}[\mathbb{F},L,d]$ (over a sufficiently large field, with $L$ a smooth multiplicative coset) with round-by-round soundness error $2^{-\lambda}$ whose query complexity is $O(\log d+\lambda\cdot\log\log d)$, compared with $O(\lambda\cdot\log d)$ for FRI; its round complexity is $O(\log d)$ and prover time is quasi-linear in $|L|$. Compiled with the BCS transform it yields a hash-based SNARG with argument size $O(\log d+\lambda\log\log d)$ Merkle openings (each of $O(\log|L|)$ hashes), and the same holds in the list-decoding regime up to the Johnson bound.

## Proof sketch

Each iteration improves the rate geometrically while reducing degree by $k$, so the number of queries needed per round to achieve $\lambda$ bits of soundness, about $\lambda/\log(1/\rho_i)$, decreases geometrically. Summing over $O(\log_k d)$ rounds gives $O(\log d+\lambda\log\log d)$. Round-by-round soundness follows from the iteration lemma and makes the BCS compilation sound in the random oracle model.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)
- [Merkle root](../../hash-functions/merkle-trees/root.md)

## Proof depends on

- [One STIR iteration: fold, shift to a smaller domain, quotient](stir-iteration.md)
- [Johnson-bound list size for Reed–Solomon codes](johnson-list-size.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
- Eli Ben-Sasson, Alessandro Chiesa, Nicholas Spooner, "Interactive Oracle Proofs", TCC (2016).
