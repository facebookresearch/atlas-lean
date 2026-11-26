# Phase error after modulus switching

Let $\mathbf{s} \in (\mathbb{Z}[X]/(X^n+1))^k$ be an integer secret and let $(\mathbf{u}, v)$ be a ciphertext over $R_q$ with integer phase representative $\varphi = \bar v - \mathbf{s}^{\mathsf T}\bar{\mathbf{u}}$. After switching to modulus $p$, the switched phase $\varphi' = v' - \mathbf{s}^{\mathsf T}\mathbf{u}'$ has an integer representative satisfying, coefficientwise,

$$
\Bigl|\varphi' - \tfrac{p}{q}\,\varphi\Bigr| \;\le\; \tfrac12\bigl(1 + \|\mathbf{s}\|_1\bigr),
$$

where $\|\mathbf{s}\|_1$ is the sum of the absolute values of all coefficients of $\mathbf{s}$. No assumption that the phase avoids wraparound is needed: integer carries absorb multiples of $q$.

## Proof sketch

Write each rounded coefficient as $(p/q)\bar x + \delta$ with $|\delta| \le 1/2$; the phase changes by $\delta_v - \mathbf{s}^{\mathsf T}\boldsymbol{\delta}_{\mathbf u}$ plus $p$ times the integer carry, and the negacyclic product of $\mathbf{s}$ with a vector of entries at most $1/2$ has coefficients at most $\|\mathbf{s}\|_1/2$.

## Depends on

- [Modulus switching of LWE ciphertexts](modulus-switching.md)

## Sources

- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
