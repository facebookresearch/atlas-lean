# VOLE-based zero-knowledge proofs for arithmetic circuits

For a public straight-line arithmetic circuit $C$ over $\mathbb{F}$ with public inputs, private inputs and a designated public output $y$, the prover authenticates every wire value with VOLE corrections, opens linear combinations to enforce public inputs, addition and constant gates and the output, and proves all multiplication gates with one batched masked multiplication check. Then: (i) for a true statement the honest prover is always accepted, and a wire assignment satisfying all linear equations and multiplication gates yields an actual private input $w$ with $C(\cdot, w) = y$; (ii) a false public statement is accepted with probability at most the batched-check bound of the VOLE multiplication check ($3/|\mathbb{F}|$ for a uniform weight vector, $(t + 2)/|\mathbb{F}|$ for powers of one scalar over $t$ multiplication gates) plus the binding error $1/|\mathbb{F}|$ of each linear opening, because the prover's corrections and linear openings are fixed before the weights and the key is sampled independently; (iii) the verifier's full view is exactly simulatable for every true statement against every verifier. For polynomial constraints of degree $d$ the QuickSilver check accepts a false constraint with probability at most $d/|\mathbb{F}|$ (at most $d/2^\lambda$ with $\lambda$-bit challenges, including grinding) and is zero knowledge using $d - 1$ additional VOLE masks.

## Proof sketch

Soundness: by IT-MAC binding the openings fix the extracted wire values, and the multiplication polynomial in $\Delta$ has nonzero leading coefficient on a false statement. Zero knowledge follows from the masked-check simulation, with linear openings reconstructed from the public statement.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](vole-correlations-and-it-macs.md)
- [Zero-knowledge interactive proofs](../zero-knowledge-interactive-proofs.md)

## Proof depends on

- [Soundness of the VOLE multiplication check](vole-multiplication-check.md)
- [Zero knowledge of masked VOLE multiplication checks](masked-multiplication-check-zero-knowledge.md)
- [Hiding of VOLE commitments and binding of IT-MAC openings](it-mac-hiding-and-binding.md)

## Sources

- Kang Yang, Pratik Sarkar, Chenkai Weng and Xiao Wang, "QuickSilver: Efficient and Affordable Zero-Knowledge Proofs for Circuits and Polynomials over Any Field", Proceedings of the 2021 ACM SIGSAC Conference on Computer and Communications Security (CCS 2021), 2021.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
