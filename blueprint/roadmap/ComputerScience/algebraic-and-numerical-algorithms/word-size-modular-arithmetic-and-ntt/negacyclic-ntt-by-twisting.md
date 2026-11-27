# Negacyclic number-theoretic transform by twisting

If $p$ is a prime with $p\equiv 1\pmod{2n}$ and $\omega$ has order $2n$, the values of a polynomial at the odd powers of $\omega$ are the $n$-point discrete Fourier transform, at $\omega^{2}$, of its coefficients twisted by $\omega^{i}$; products in $\mathbb{Z}_p[\alpha]/(\alpha^n+1)$ become pointwise products of these vectors.

Let $n$ be a power of two, let $p$ be a prime with $2n\mid p-1$, and let $\omega\in\mathbb{Z}_p$ have multiplicative order $2n$. Then the $n$ odd powers $\omega,\omega^{3},\dots,\omega^{2n-1}$ are exactly the roots of $\alpha^{n}+1$ in $\mathbb{Z}_p$, and the evaluation map

$$
\mathbb{Z}_p[\alpha]/(\alpha^{n}+1)\longrightarrow\mathbb{Z}_p^{n},\qquad a\longmapsto\bigl(a(\omega^{2j+1})\bigr)_{0\le j<n},
$$

is a bijection that sends products to componentwise products. For $a=\sum_{i<n}a_i\alpha^{i}$ these values are

$$
a(\omega^{2j+1})=\sum_{i=0}^{n-1}\bigl(\omega^{i}a_i\bigr)\,(\omega^{2})^{ij}\qquad(0\le j<n),
$$

the length-$n$ discrete Fourier transform over $\mathbb{Z}_p$, with the primitive $n$-th root of unity $\omega^{2}$, of the twisted vector $(\omega^{0}a_0,\omega^{1}a_1,\dots,\omega^{n-1}a_{n-1})$. Hence a product in $\mathbb{Z}_p[\alpha]/(\alpha^{n}+1)$ is determined by twisting both inputs, applying an $n$-point fast Fourier transform over $\mathbb{Z}_p$, and multiplying pointwise, without padding to length $2n$.

## Depends on

- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](../../cryptography/public-key/lattice-and-code-based-cryptography/lattice-problems/negacyclic-ring.md)

## Proof depends on

- [CRT packing of plaintext slots](../../cryptography/public-key/homomorphic-encryption/leveled-packed-fhe-bgv-and-bfv/crt-plaintext-slots.md)

## Expansion

The bijection with componentwise products is the Chinese remainder isomorphism for the complete splitting of $\alpha^{n}+1$ over $\mathbb{Z}_p$, the same one that gives plaintext slots for a prime plaintext modulus congruent to $1$ modulo $2n$. The displayed formula follows from $\omega^{(2j+1)i}=\omega^{i}(\omega^{2})^{ij}$.

Expansion requirements: (i) recovering the product's coefficients needs the inverse transform over $\mathbb{Z}_p$ (inverse DFT with the factor $n^{-1}$, followed by untwisting with $\omega^{-i}$); (ii) the $O(n\log n)$ cost needs the radix-two fast Fourier transform over a field with a primitive $n$-th root of unity.

## Sources

- Vadim Lyubashevsky, Daniele Micciancio, Chris Peikert, Alon Rosen, "SWIFFT: A Modest Proposal for FFT Hashing", Fast Software Encryption (FSE 2008), LNCS, pp. 54–72, DOI [10.1007/978-3-540-71039-4_4](https://doi.org/10.1007/978-3-540-71039-4_4): §1.1 (multiply row $i$ by $\omega^{i-1}$, then an FFT over $\mathbb{Z}_p$; the step is invertible) and §2.1 (prime $p$ with $2n\mid p-1$, $\omega$ of order $2n$, odd powers as the roots of $\alpha^{n}+1$, products determined by these values, $n$-dimensional FFT with $\omega^{2}$); authors' copy.
- Zhichuang Liang, Yunlei Zhao, "Number Theoretic Transform and Its Applications in Lattice-based Cryptosystems: A Survey", arXiv:2211.13546v1: §3.2, Proposition 3.4 (negative wrapped convolution property) (supporting survey).
