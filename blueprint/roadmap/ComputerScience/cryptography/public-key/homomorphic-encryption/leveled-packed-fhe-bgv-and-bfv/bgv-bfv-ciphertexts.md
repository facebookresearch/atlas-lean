# BGV and BFV ring ciphertexts

Let $R=\mathbb{Z}[X]/(X^{N}+1)$ with $N$ a power of two, $R_q=R/qR$, a plaintext modulus $t$ coprime to $q$, and a secret $s\in R$ with small coefficients. A *BGV ciphertext* of $m\in R_t$ is $(c_0,c_1)\in R_q^{2}$ with $c_0+c_1s\equiv m+te\pmod q$ for a small $e\in R$ (least-significant-bit encoding); it decrypts correctly as $m=((c_0+c_1s)\bmod q)\bmod t$ when $\|m+te\|_\infty< q/2$. A *BFV ciphertext* of $m$ satisfies $c_0+c_1s\equiv\Delta m+e\pmod q$ with $\Delta=\lfloor q/t\rfloor$ (most-significant-bit encoding), decrypting as $m=\lfloor t(c_0+c_1s\bmod q)/q\rceil\bmod t$ when $\|e\|_\infty$ is below about $\Delta/2$.

## Depends on

- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption-correctness-and.md)
- [Hardness of Ring-LWE from worst-case problems on ideal lattices](../../isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/ring-lwe-hardness.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
- Junfeng Fan, Frederik Vercauteren, "Somewhat Practical Fully Homomorphic Encryption", IACR ePrint 2012/144 (2012).
