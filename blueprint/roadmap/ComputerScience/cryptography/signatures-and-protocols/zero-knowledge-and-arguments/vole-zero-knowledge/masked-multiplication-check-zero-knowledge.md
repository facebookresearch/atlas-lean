# Zero knowledge of masked VOLE multiplication checks

In the masked multiplication check, the prover blinds both reply coefficients with a fresh ideal VOLE coordinate that receives no correction, after all wire corrections have been sent and before the verifier's public weights are chosen. Adding the mask preserves completeness at every key. Against every verifier strategy, including one that chooses the weights adaptively from its key share, the corrections and its private coins and retains arbitrary state, the verifier's full view is exactly simulatable from its own key share: the simulator samples uniform corrections, uniform masked replies satisfying the verification equation, and runs the verifier. Every simulated transcript satisfies the masked equation.

## Proof sketch

Corrections are one-time-pad encryptions of the witness under uniform VOLE vectors, and the masked reply is uniform subject to the single linear relation the verifier checks.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](vole-correlations-and-it-macs.md)

## Proof depends on

- [Soundness of the VOLE multiplication check](vole-multiplication-check.md)

## Sources

- Kang Yang, Pratik Sarkar, Chenkai Weng and Xiao Wang, "QuickSilver: Efficient and Affordable Zero-Knowledge Proofs for Circuits and Polynomials over Any Field", Proceedings of the 2021 ACM SIGSAC Conference on Computer and Communications Security (CCS 2021), 2021.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
