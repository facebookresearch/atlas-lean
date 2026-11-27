# G-stability

Let $G = (g_{ij})$ be a symmetric positive definite $k \times k$ matrix. For a block $Z_n = (z_{n+k-1}^T, \dots, z_n^T)^T \in \mathbb{R}^{mk}$ of $k$ consecutive vectors $z_{n+j} \in \mathbb{R}^m$, the *G-norm* is

$$\|Z_n\|_G = \Big(\sum_{i=1}^k \sum_{j=1}^k g_{ij} \langle z_{n+k-i}, z_{n+k-j} \rangle\Big)^{1/2}.$$

Let $\rho$ and $\sigma$ be the characteristic polynomials of a linear multistep method with $s = \sigma(1) \ne 0$. Its [one-leg twin](one-leg-twin.md) $\rho(E) y_n = h\, s\, f(\sigma(E) y_n / s)$, which is $\rho(E) y_n = h f(\sigma(E) y_n)$ when $\sigma(1) = 1$, is *G-stable* if there is such a $G$ with

$$\|Z_{n+1}\|_G^2 - \|Z_n\|_G^2 \le \frac{2\, \langle \rho(E) z_n,\ \sigma(E) z_n \rangle}{\sigma(1)^2}$$

for every sequence $(z_n)$ in $\mathbb{R}^m$ and every $n$. The condition does not change when $\rho$ and $\sigma$ are multiplied by a common nonzero constant.

## Depends on

- [One-leg twin of a linear multistep method](one-leg-twin.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, the definition of the G-norm and Definition 17 (after Dahlquist, 1975). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
