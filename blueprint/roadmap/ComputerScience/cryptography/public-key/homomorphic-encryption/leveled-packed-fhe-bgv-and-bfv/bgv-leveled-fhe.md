# BGV: leveled fully homomorphic encryption without bootstrapping

For every depth bound $L$, assuming Ring-LWE (or LWE, with a matrix variant) with modulus-to-noise ratio $2^{O(L\log\lambda)}$ and circular security of the relinearization keys (avoidable with a fresh key per level), there is a leveled fully homomorphic encryption scheme for arithmetic circuits of depth $L$ over $\mathbb{F}_t$ in which noise is managed by modulus switching along a chain of $L+1$ moduli. In the Ring-LWE instantiation the per-gate computation is $\widetilde{O}(\lambda\cdot L^{3})$, and with batching over CRT slots the amortized cost per slot operation is quasi-linear in $\lambda$ for depth $L=O(\log\lambda)$ settings. Combined with bootstrapping as an optimization, the per-gate overhead becomes $\widetilde{O}(\lambda^{2})$, independent of $L$.

## Proof sketch

Use the modulus-chain lemma inductively: each multiplicative level is followed by modulus switching, keeping noise bounded relative to the current modulus, so decryption is correct at level $0$. Security at each level reduces to Ring-LWE for the corresponding modulus. Cost: ring elements have $\widetilde{O}(\lambda L)$ bits for dimension $\widetilde{O}(\lambda L)$ needed for security against $2^{\lambda}$ attacks with modulus $2^{O(L\log\lambda)}$, and multiplication of ring elements with key switching costs $\widetilde{O}(\lambda L^{3})$ overall per gate.

## Depends on

- [Hardness of Ring-LWE from worst-case problems on ideal lattices](../../isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/ring-lwe-hardness.md)
- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption-correctness-and.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Noise management along a BGV modulus chain](bgv-modulus-chain.md)
- [CRT packing of plaintext slots](crt-plaintext-slots.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
