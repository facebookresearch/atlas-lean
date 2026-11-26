# CRT packing of plaintext slots

Let $t$ be a prime with $t\equiv 1\pmod{2N}$. Then $X^{N}+1$ splits into $N$ distinct linear factors over $\mathbb{F}_t$, and the Chinese remainder theorem gives a ring isomorphism $R_t=\mathbb{F}_t[X]/(X^{N}+1)\cong\mathbb{F}_t^{N}$, $m\mapsto(m(\zeta^{2i+1}))_{0\le i< N}$, where $\zeta$ is a primitive $2N$-th root of unity in $\mathbb{F}_t$. Homomorphic addition and multiplication of ciphertexts therefore act slotwise (SIMD) on vectors of $N$ elements of $\mathbb{F}_t$. More generally, if $t$ has order $d$ modulo $2N$, $R_t\cong\mathbb{F}_{t^{d}}^{N/d}$.

## Proof sketch

The roots of $X^{N}+1$ are the primitive $2N$-th roots of unity, which exist in $\mathbb{F}_t$ exactly when $2N\mid t-1$; they are the $N$ odd powers of $\zeta$ and are distinct, so CRT applies. For general $t$, the factors correspond to the orbits of multiplication by $t$ on the odd residues modulo $2N$, each of size $d$.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Sources

- Nigel P. Smart, Frederik Vercauteren, "Fully Homomorphic SIMD Operations", Designs, Codes and Cryptography (2014).
- Craig Gentry, Shai Halevi, Nigel P. Smart, "Homomorphic Evaluation of the AES Circuit", CRYPTO (2012).
