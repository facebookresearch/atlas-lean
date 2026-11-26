# Batched Reed–Solomon proximity IOPs from Ligero

The Ligero test for a matrix of claimed Reed–Solomon codewords can be batched with a full random vector $r \in \mathbb{F}^m$ (affine batching) or with the powers of one scalar (curve batching). Both reductions are perfectly complete on honestly encoded matrices and read the matrix only at the $q$ queried columns. Affine batching is round-by-round sound up to the Johnson bound: for distance $e$ with $e/n \le 1 - \sqrt\rho - \eta$, a matrix $e$-far from the interleaved code survives the batching round with probability at most the Johnson-regime error of the Reed–Solomon proximity-gap theorem of Ben-Sasson et al. (Theorems 1.2 and 1.6), $k^2 / \bigl((2\min(\eta, \sqrt{\rho}/20))^7\,|\mathbb{F}|\bigr)$, where $k$ is the code dimension and $\rho = k/n$; curve batching is round-by-round sound in the unique-decoding regime $2e + k \le n$ with error $(m-1)n/|\mathbb{F}|$ (Theorem 1.5). Combined with the column check and the BCS transform, these give non-interactive proximity proofs sound in the random oracle model against every adaptive prover.

## Proof sketch

Apply the affine-line and curve proximity-gap theorems to the rows of the matrix, then the column-check escape bound, and compile with BCS.

## Depends on

- [Ligero interleaved proximity test](ligero-interleaved-proximity.md)

## Proof depends on

- [Proximity gaps and correlated agreement for Reed–Solomon codes](../fri-proximity-protocol/reed-solomon-proximity-gaps.md)
- [Soundness and straight-line knowledge soundness of the BCS transform](../interactive-oracle-proofs/bcs-soundness.md)

## Sources

- Scott Ames, Carmit Hazay, Yuval Ishai and Muthuramakrishnan Venkitasubramaniam, "Ligero: Lightweight Sublinear Arguments Without a Trusted Setup", Proceedings of the 2017 ACM SIGSAC Conference on Computer and Communications Security (CCS 2017), 2017.
- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
