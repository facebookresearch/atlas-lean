# Decryption correctness of HQC

For honestly generated HQC keys and ciphertexts, the decoder input equals the encoded message plus the truncation of the error $e' = x r_2 - r_1 y + e$. If the truncated error has Hamming weight at most the decoding radius of the public code, decryption returns $m$. Consequently the decryption failure probability of HQC-PKE is at most the probability, over the independent draws of $y, x, r_2, e, r_1$ with their prescribed weights, that the decoder of the public code fails on $m\mathbf{G} + \mathrm{trunc}(e')$; this is the $\delta$ used in the Fujisaki–Okamoto transform that turns HQC-PKE into the HQC KEM.

## Proof sketch

Substitute $s = x + hy$ and $u = r_1 + h r_2$: the terms $h y r_2$ cancel in $v - uy$ by commutativity of $\mathcal{R}$, leaving the stated error. Correctness then follows from the decoding guarantee of the concatenated code.

## Depends on

- [HQC public-key encryption](hqc-public-key-encryption.md)
- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](../../chosen-ciphertext-security/fujisaki-okamoto-kem-transforms/pke-with-explicit-coins.md)

## Sources

- Philippe Gaborit et al., "Hamming Quasi-Cyclic (HQC)", Version 5.1, November 9, 2026.
