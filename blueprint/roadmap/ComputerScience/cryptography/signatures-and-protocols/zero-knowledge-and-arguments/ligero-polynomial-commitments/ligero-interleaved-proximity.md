# Ligero interleaved proximity test

Let $C \subseteq \mathbb{F}^n$ be a linear code (e.g. Reed–Solomon with a Vandermonde generator $G$) and let $M \in \mathbb{F}^{m \times n}$ be a matrix whose rows are claimed to be codewords, $M = U G$. In the Ligero test the verifier sends a random vector $r \in \mathbb{F}^m$ (or the powers of a random scalar), the prover sends $v$ with claimed $r^{\mathsf T} M = v^{\mathsf T} G$, and the verifier checks this equation on $q$ uniformly random columns. Honestly encoded matrices are always accepted, and the test reads $M$ only at the queried columns. If $r^{\mathsf T}M$ and $v^{\mathsf T}G$ differ on more than $e$ columns, the column check passes with probability at most $(1 - e/n)^q$. Call $M$ *$e$-far* from the interleaved code $C^m$ if there is no set of at most $e$ columns outside which every row of $M$ agrees with a codeword, and call a word $e$-close to $C$ if it differs from some codeword in at most $e$ positions. If $C$ is an arbitrary $[n, k, d]$ linear code, $e \le \lfloor (d-1)/3 \rfloor$ and $M$ is $e$-far from $C^m$, then $r^{\mathsf T}M$ is $e$-close to $C$ with probability at most $(e+1)/|\mathbb{F}| \le n/|\mathbb{F}|$ over a uniform $r \in \mathbb{F}^m$ (Diamond and Posen, Theorem 1 and Remark 1). If $C$ is a Reed–Solomon code of rate $\rho$ and $0 < e/n < 1 - \sqrt{\rho}$, let $\varepsilon$ be the error parameter of the proximity gap of Ben-Sasson et al. (Theorem 1.2): $\varepsilon = n/|\mathbb{F}|$ when $e/n < (1-\rho)/2$, and their Johnson-regime error $\varepsilon_J$ above that. If $M$ is $e$-far from $C^m$, then $r^{\mathsf T}M$ is $e$-close to $C$ with probability at most $\varepsilon$ over a uniform $r \in \mathbb{F}^m$ (their Theorem 1.6), and at most $(m-1)\varepsilon$ when $r = (1, z, \dots, z^{m-1})$ for a uniform scalar $z$ (their Theorem 1.5). Combined with an evaluation check, this gives an IOP for polynomial evaluation claims sound against arbitrary provers, and with the BCS transform a polynomial commitment scheme in the random oracle model.

## Proof sketch

A random linear combination of the rows of a matrix far from the interleaved code is far from the code except with small probability (a proximity gap for affine spaces or curves); applied to the affine space or curve through the rows of $M$, the cited theorems say that if more combinations than the stated error fraction were $e$-close, the rows would have correlated agreement outside at most $e$ columns, i.e. $M$ would be within $e$ columns of $C^m$. The column check catches a disagreement set of size more than $e$ with probability $1 - (1 - e/n)^q$.

## Depends on

- [Reed-Solomon code](../../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)
- [Polynomial commitment schemes](../polynomial-commitment-schemes.md)
- [Public-coin interactive oracle proofs](../interactive-oracle-proofs/public-coin-iop.md)

## Proof depends on

- [Proximity gaps and correlated agreement for Reed–Solomon codes](../fri-proximity-protocol/reed-solomon-proximity-gaps.md)
- [Random linear combination batching of evaluation claims](batched-evaluation-claims.md)

## Sources

- Scott Ames, Carmit Hazay, Yuval Ishai and Muthuramakrishnan Venkitasubramaniam, "Ligero: Lightweight Sublinear Arguments Without a Trusted Setup", Proceedings of the 2017 ACM SIGSAC Conference on Computer and Communications Security (CCS 2017), 2017.
- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023, Theorem 1.2 (error parameters), Theorem 1.5 (curves) and Theorem 1.6 (affine spaces).
- Benjamin E. Diamond and Jim Posen, "Proximity Testing with Logarithmic Randomness", IACR Communications in Cryptology 1(1), 2024, Theorem 1 (any $[n, k, d]$ code and $e \le \lfloor (d-1)/3 \rfloor$: an affine line with more than an $(e+1)/q$ fraction of $e$-close points has interleaved distance at most $e$) and Remark 1 (the same for affine subspaces of any dimension).
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
