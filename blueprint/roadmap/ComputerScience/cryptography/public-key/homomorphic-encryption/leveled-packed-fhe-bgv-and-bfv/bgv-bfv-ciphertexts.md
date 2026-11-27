# BGV and BFV ring ciphertexts

Let $R=\mathbb{Z}[X]/(X^{N}+1)$ with $N$ a power of two, $R_q=R/qR$, a plaintext modulus $t$ coprime to $q$, and a secret $s\in R$ with small coefficients. A *BGV ciphertext* of $m\in R_t$ is $(c_0,c_1)\in R_q^{2}$ with $c_0+c_1s\equiv m+te\pmod q$ for a small $e\in R$ (least-significant-bit encoding); it decrypts correctly as $m=((c_0+c_1s)\bmod q)\bmod t$ when $\|m+te\|_\infty< q/2$. Write $[x]_q$ for the centered representative of $x$ modulo $q$, with coefficients in $[-q/2,q/2)$. A *BFV ciphertext* of $m\in R_t$ is $(c_0,c_1)\in R_q^{2}$ with inherent noise $v\in R$ defined by $[c_0+c_1s]_q=[\Delta[m]_t+v]_q$, where $\Delta=\lfloor q/t\rfloor$ (most-significant-bit encoding). Its decryption $\mathrm{DecFV}$ outputs $\bigl[\lfloor\tfrac{t}{q}[c_0+c_1s]_q\rceil\bigr]_t$, which equals $[m]_t$ when $\|v\|_\infty<(\Delta-|q|_t)/2$, where $|q|_t=q\bmod t\in[0,t)$.

## Depends on

- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption-correctness-and.md)
- [Hardness of Ring-LWE from worst-case problems on ideal lattices](../../isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/ring-lwe-hardness.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", SAC 2016, LNCS 10532 (2017), §§2–4 (`DecFV`, `MultFV`, `RelinFV`), DOI 10.1007/978-3-319-69453-5_23.
