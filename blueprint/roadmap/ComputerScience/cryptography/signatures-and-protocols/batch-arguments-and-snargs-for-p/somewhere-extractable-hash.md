# Somewhere extractable (somewhere statistically binding) hash functions

A *somewhere statistically binding (SSB) hash* is a keyed hash with local openings, $H_{hk}:\Sigma^{N}\to\{0,1\}^{\mathrm{poly}(\lambda,\log N)}$, whose key generation takes a hidden index $i\in[N]$: keys for different indices are computationally indistinguishable (index hiding), and for a key generated at index $i$, no digest has two valid local openings at position $i$ to different values, even for an unbounded adversary. A *somewhere extractable* hash or commitment additionally outputs, with the key, a trapdoor from which an extraction algorithm recovers from any digest the unique value that can be opened at the bound position; the extraction-correctness requirement implies statistical binding there. Variants bind a hidden set of positions at once, with a trapdoor per position. SSB hashes exist under LWE (and more generally from leveled homomorphic encryption), with digest, opening and verification sizes $\mathrm{poly}(\lambda,\log N)$, and the construction is somewhere extractable.

## Depends on

- [Merkle root](../../hash-functions/merkle-trees/root.md)

## Sources

- Pavel Hubáček, Daniel Wichs, "On the Communication Complexity of Secure Function Evaluation with Long Output", ITCS (2015) (the SSB notion and its construction).
- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808, Section 3.5 and Theorem 4 (somewhere extractable commitments for hidden sets of positions, from LWE).
- Yael Tauman Kalai, Vinod Vaikuntanathan, Rachel Yun Zhang, "Somewhere Statistical Soundness, Post-Quantum Security, and SNARGs", TCC (2021), Definition 3.1 and Theorem 3.3 (extractable SSB hashes).
