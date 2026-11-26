# Correctness modulo the plaintext modulus versus integer correctness

BGV and BFV evaluation is correct modulo $t$: decryption of $\mathrm{Eval}(f,\mathrm{Enc}(m_1),\dots,\mathrm{Enc}(m_k))$ yields $f(m_1,\dots,m_k)\bmod t$ for an arithmetic circuit $f$ over $\mathbb{Z}$ within the noise budget. If $m_i$ and every intermediate value of the evaluation of $f$ over $\mathbb{Z}$ lie in $(-t/2,t/2)$, then the centered decryption equals the integer value of $f$; without such a range bound, the decrypted value may differ from the integer result by a multiple of $t$. Integer computations on unbounded values therefore require either a large $t$ chosen from a range analysis or CRT decomposition over several plaintext moduli.

## Proof sketch

Reduction modulo $t$ is a ring homomorphism from $\mathbb{Z}$, so the computation commutes with it. The centered representative of a residue modulo $t$ is the unique integer in $(-t/2,t/2]$ in its class, which equals the integer result exactly when the latter lies in that range.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Proof depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
- Junfeng Fan, Frederik Vercauteren, "Somewhat Practical Fully Homomorphic Encryption", IACR ePrint 2012/144 (2012).
