# Universal SNARGs for NP from proofs of correctness

Assume a (leveled or unleveled) fully homomorphic encryption scheme and a non-interactive batch argument for NP. For any parameters $\ell,L$, there is a candidate SNARG for every NP language with proof length $\ell\cdot\mathrm{poly}(\lambda)$, common reference string length $L\cdot\mathrm{poly}(\lambda)$ and transparent setup, which is non-adaptively sound provided there exists any SNARG for that language with proof size $\ell$ and reference string size $L$ whose completeness has an Extended Frege proof of size $L$. The underlying SNARG may be relaxed to any two-message privately verifiable argument with first message of length $L$ and second of length $\ell$.

## Proof sketch

The universal verifier checks, inside an FHE-based private-verification shell aggregated with BARGs, a propositional proof (in Extended Frege) that the hypothetical SNARG is complete; local checkability of Extended Frege lines lets BARGs certify the propositional proof succinctly, and soundness transfers from the hypothetical SNARG via the soundness of propositional proofs.

## Depends on

- [Non-interactive batch arguments for NP](batch-argument.md)
- [Homomorphic encryption: correctness and compactness](../../public-key/homomorphic-encryption/homomorphic-encryption-correctness-and.md)
- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)

## Proof depends on

- [No black-box reduction proves adaptive SNARGs for NP sound from falsifiable assumptions](gentry-wichs-barrier.md)
- [Batch arguments for NP from LWE](cjj-barg-from-lwe.md)

## Sources

- Zhengzhong Jin, Yael Tauman Kalai, Alex Lombardi, Surya Mathialagan, "Universal SNARGs for NP from Proofs of Correctness", STOC (2025), IACR ePrint 2024/2015.
