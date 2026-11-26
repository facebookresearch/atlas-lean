# Ligero interleaved proximity test

Let $C \subseteq \mathbb{F}^n$ be a linear code (e.g. Reed–Solomon with a Vandermonde generator $G$) and let $M \in \mathbb{F}^{m \times n}$ be a matrix whose rows are claimed to be codewords, $M = U G$. In the Ligero test the verifier sends a random vector $r \in \mathbb{F}^m$ (or the powers of a random scalar), the prover sends $v$ with claimed $r^{\mathsf T} M = v^{\mathsf T} G$, and the verifier checks this equation on $q$ uniformly random columns. Honestly encoded matrices are always accepted, and the test reads $M$ only at the queried columns. If $r^{\mathsf T}M$ and $v^{\mathsf T}G$ differ on more than $e$ columns, the column check passes with probability at most $(1 - e/n)^q$. If $M$ is $e$-far from the interleaved code $C^m$ (with $e$ below a third of the minimum distance, or up to the Johnson radius in the proximity-gap version), then $r^{\mathsf T}M$ is $e$-far from $C$ except with probability at most $n/|\mathbb{F}|$ over a uniform $r \in \mathbb{F}^m$ (at most $(m-1)n/|\mathbb{F}|$ for powers of a random scalar) in the unique-decoding case, and at most the Johnson-regime error of the proximity-gap theorem up to the Johnson radius. Combined with an evaluation check, this gives an IOP for polynomial evaluation claims sound against arbitrary provers, and with the BCS transform a polynomial commitment scheme in the random oracle model.

## Proof sketch

A random linear combination of the rows of a matrix far from the interleaved code is far from the code except with small probability (a proximity gap for lines or curves). The column check catches a disagreement set of size more than $e$ with probability $1 - (1 - e/n)^q$.

## Depends on

- [Reed-Solomon code](../../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)
- [Polynomial commitment schemes](../polynomial-commitment-schemes.md)
- [Public-coin interactive oracle proofs](../interactive-oracle-proofs/public-coin-iop.md)

## Proof depends on

- [Proximity gaps and correlated agreement for Reed–Solomon codes](../fri-proximity-protocol/reed-solomon-proximity-gaps.md)
- [Random linear combination batching of evaluation claims](batched-evaluation-claims.md)

## Sources

- Scott Ames, Carmit Hazay, Yuval Ishai and Muthuramakrishnan Venkitasubramaniam, "Ligero: Lightweight Sublinear Arguments Without a Trusted Setup", Proceedings of the 2017 ACM SIGSAC Conference on Computer and Communications Security (CCS 2017), 2017.
- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
