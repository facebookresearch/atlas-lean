# Exact sampling of LWE key-generation inputs from fair coins

At modulus $q = 2^w$: a uniform residue is obtained exactly from $w$ fair bits, a uniform vector (matrix) from disjoint blocks of $w$ bits per entry, and a centered binomial error of width $\eta$ from $2\eta$ bits; consequently all inputs of LWE key generation, the secret, the public matrix part and the errors, are independent functions of disjoint parts of one finite uniform tape. The generated public matrix $[\,B t + e \mid B\,]$ satisfies $[\,B t + e \mid B\,](1, -t)^{\mathsf T} = e$, so it is exactly a decision-LWE sample with the secret vector $(1, -t)$. For general moduli, sampling each coefficient from $\lceil\log_2 q\rceil + p$ fair bits by reduction gives a law within statistical distance $2^{-p}$ per coefficient of uniform.

## Proof sketch

For a power-of-two modulus the binary expansion of $w$ bits is a bijection onto $\mathbb{Z}_{2^w}$. For general $q$, the reduction modulo $q$ of a uniform integer below $2^{b}$ hits each residue $\lfloor 2^b/q\rfloor$ or $\lceil 2^b/q \rceil$ times.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [The centered binomial distribution](../module-lattice-encryption/centered-binomial-distribution.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
