# Approximate correctness of CKKS homomorphic evaluation

Let $f$ be an arithmetic circuit over $\mathbb{C}$ of multiplicative depth $L'\le L$, applied slotwise to vectors $\mathbf{z}_1,\dots,\mathbf{z}_k\in\mathbb{C}^{N/2}$ with $\|\mathbf{z}_i\|_\infty\le 1$, in which each multiplication is followed by rescaling. Assuming Ring-LWE and circular security of the relinearization and rotation keys, CKKS evaluation yields a ciphertext at level $L-L'$ whose decryption $\mathbf{w}$ satisfies $\|\mathbf{w}-f(\mathbf{z}_1,\dots,\mathbf{z}_k)\|_\infty\le\epsilon$, where $\epsilon$ is bounded by a sum over gates of the per-gate error terms (encoding error $N/(2\Delta)$, fresh error, key-switching and rescaling errors divided by $\Delta$), each amplified by the Lipschitz constant of the subsequent computation. In particular, for bounded-degree polynomial evaluation the output has about $\log_2\Delta-O(\log N+L')$ bits of precision.

## Proof sketch

Induct over the circuit using the multiplication-error lemma and the analogous additive bounds for additions, scalar multiplications and rotations (key switching for Galois automorphisms). Security is IND-CPA from Ring-LWE as for BGV, with the usual circular security requirement for evaluation keys.

## Depends on

- [Error propagation of CKKS multiplication with relinearization and rescaling](ckks-multiplication-error.md)
- [Rounding error of CKKS encoding](ckks-encoding-error.md)
- [Galois automorphisms rotate plaintext slots](../leveled-packed-fhe-bgv-and-bfv/galois-slot-rotations.md)

## Proof depends on

- [Error propagation of CKKS multiplication with relinearization and rescaling](ckks-multiplication-error.md)
- [Rounding error of CKKS encoding](ckks-encoding-error.md)

## Sources

- Jung Hee Cheon, Andrey Kim, Miran Kim, Yongsoo Song, "Homomorphic Encryption for Arithmetic of Approximate Numbers", ASIACRYPT (2017), IACR ePrint 2016/421.
