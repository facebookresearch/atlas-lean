# Somewhere extractable (somewhere statistically binding) hash functions

A *somewhere statistically binding (SSB) hash* is a keyed hash $H_{hk}:\Sigma^{N}\to\{0,1\}^{\mathrm{poly}(\lambda,\log N)}$ with local openings, where keys can be generated binding to a hidden index $i\in[N]$: in that mode, any digest has at most one valid opening at position $i$ (statistical binding), and keys for different indices are computationally indistinguishable. A *somewhere extractable* hash additionally provides a trapdoor that extracts the unique value at position $i$ from the digest. SSB hashes exist under LWE (and other standard assumptions), with digest and opening sizes $\mathrm{poly}(\lambda,\log N)$.

## Depends on

- [Merkle root](../../hash-functions/merkle-trees/root.md)

## Sources

- Pavel Hubáček, Daniel Wichs, "On the Communication Complexity of Secure Function Evaluation with Long Output", ITCS (2015).
- Yael Tauman Kalai, Omer Paneth, Lisa Yang, "How to Delegate Computations Publicly", STOC (2019), IACR ePrint 2018/776.
