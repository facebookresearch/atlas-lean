# VOLE-in-the-head

*VOLE-in-the-head* makes VOLE-based zero knowledge publicly verifiable and non-interactive. The prover expands an *all-but-one vector commitment* (a GGM-style tree of $2^d$ leaf seeds committed by hashing the leaves) into $2^d$ rows $r_0, \dots, r_{2^d - 1} \in \mathbb{F}_2^{\hat\ell}$ and converts them into a small-field VOLE correlation: at tree level $j$, the XOR of the odd rows in each adjacent pair recursively gives column $v_j$, and $u = \bigoplus_i r_i$. After the verifier (or Fiat–Shamir) reveals a challenge $\Delta \in \{0,1\}^d$ and the prover opens all leaves except the one at index $\Delta$, the verifier recomputes $q_j = v_j \oplus \Delta_j u$ for every level $j$. Several small VOLE instances (repetitions) are combined into one VOLE over $\mathbb{F}_{2^\lambda}$, with a universal-hash consistency check (VOLEHash) on the $u$ vectors. FAEST instantiates this with AES or Even–Mansour as the one-way function; MQOM with multivariate quadratic systems over correlated trees.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](../../zero-knowledge-and-arguments/vole-zero-knowledge/vole-correlations-and-it-macs.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Merkle root](../../../hash-functions/merkle-trees/root.md)

## Sources

- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
- Carsten Baum et al., "FAEST v3: Algorithm Specifications", FAEST Team, 2026.
- Ryad Benadjila, Charles Bouillaguet, Thibauld Feneuil and Matthieu Rivain, "MQOM: MQ on my Mind: Algorithm Specifications and Supporting Documentation", Version 3.0, August 31, 2026.
