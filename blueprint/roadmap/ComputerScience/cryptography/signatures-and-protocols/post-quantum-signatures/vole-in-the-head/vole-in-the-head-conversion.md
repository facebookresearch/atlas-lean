# Correctness of the VOLE-in-the-head conversion

For consistent prover and verifier conversions of an all-but-one vector commitment of depth $d$, in which the verifier knows all rows except the one at index $\Delta$, the outputs satisfy the VOLE correlation $q_j = v_j \oplus \Delta_j\, u$ at every tree level $j$; hence the converted values form a valid VOLE correlation over $\mathbb{F}_2$ with key $\Delta$. In FAEST v3, the first $\lambda - w_{\mathrm{grind}}$ bits of the third Fiat–Shamir challenge are split consecutively among the repetitions, the first group receiving one more bit each, and the slices exactly cover the non-grinding prefix; in MQOM's correlated tree with heap indexing, the hidden node moves to its parent at each step and the sibling path from the leaf to the root consists of nonzero indices.

## Proof sketch

The row with index $\Delta$ contributes to $v_j$ exactly when $\Delta_j = 1$, and the verifier's reconstruction without that row differs from the prover's by $\Delta_j$ times the XOR of all rows, which is $u$.

## Depends on

- [VOLE-in-the-head](vole-in-the-head.md)

## Sources

- Carsten Baum et al., "FAEST v3: Algorithm Specifications", FAEST Team, 2026.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
- Ryad Benadjila, Charles Bouillaguet, Thibauld Feneuil and Matthieu Rivain, "MQOM: MQ on my Mind: Algorithm Specifications and Supporting Documentation", Version 3.0, August 31, 2026.
