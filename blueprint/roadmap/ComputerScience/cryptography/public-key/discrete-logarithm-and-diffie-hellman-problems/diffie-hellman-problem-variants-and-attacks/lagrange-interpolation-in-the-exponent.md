# Lagrange interpolation in the exponent

Let $q$ be prime, $J \subseteq \mathbb{Z}_q$ a set of $t$ distinct nodes and $j^* \in \mathbb{Z}_q$. For every polynomial $\omega$ over $\mathbb{Z}_q$ of degree less than $t$,

$$\omega(j^*) = \sum_{j \in J} \lambda_j\, \omega(j), \qquad \lambda_j = \prod_{j' \in J \setminus \{j\}} \frac{j^* - j'}{j - j'}.$$

Consequently, in a group of order $q$ with generator $g$, $g^{\omega(j^*)} = \prod_{j \in J} \bigl(g^{\omega(j)}\bigr)^{\lambda_j}$, and the coefficients $\lambda_j$ are computable in time polynomial in $\log q$ and $t$.

## Proof sketch

Both sides are polynomials of degree less than $t$ in the free variable agreeing on the $t$ nodes, by the defining property $\lambda_j(j') = [j = j']$.

## Depends on

- [Cyclic and prime-order group families](cyclic-group-families.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- A. Shamir, "How to Share a Secret", Communications of the ACM 22(11), 1979.
