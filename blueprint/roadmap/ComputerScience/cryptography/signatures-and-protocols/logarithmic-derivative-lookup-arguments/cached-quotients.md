# Cached quotients make table commitments reusable

Let $V\le\mathbb{F}^{\times}$ have order $N$, $Z_V(X)=X^{N}-1$, $L_i$ the Lagrange basis of $V$, and $T(X)=\sum_it_iL_i(X)$ the table polynomial. For each $i$ the polynomial $L_i(X)(T(X)-t_i)$ vanishes on $V$, so $Q_i(X)=L_i(X)(T(X)-t_i)/Z_V(X)$ is a polynomial. For $\beta\in\mathbb{F}$ and $A_i=m_i/(t_i+\beta)$, the polynomial $A(X)=\sum_iA_iL_i(X)$ and $m(X)=\sum_im_iL_i(X)$ satisfy

$$
A(X)(T(X)+\beta)-m(X)=Z_V(X)\sum_{i}A_iQ_i(X).
$$

Hence, after precomputing KZG commitments $[Q_i]$ once in time $O(N\log N)$, the prover commits to the quotient with $|\{i:m_i\ne 0\}|\le n$ group operations, independent of $N$.

## Proof sketch

Expand $A(X)(T(X)+\beta)-m(X)=\sum_iA_iL_i(X)(T(X)-t_i)+\sum_iL_i(X)\bigl(A_i(t_i+\beta)-m_i\bigr)$. The second sum vanishes by the choice of $A_i$, and the first equals $Z_V\sum_iA_iQ_i$ by definition of $Q_i$. Only indices with $m_i\ne 0$ have $A_i\ne 0$.

## Depends on

- [Security of KZG polynomial commitments](../zero-knowledge-and-arguments/security-of-kzg-polynomial-commitments.md)

## Proof depends on

- [Lagrange basis over a multiplicative subgroup](../plonkish-polynomial-iops/lagrange-basis-subgroup.md)
- [Logarithmic-derivative characterization of set inclusion](logup-lemma.md)
- [Vanishing on a multiplicative subgroup and the quotient test](../plonkish-polynomial-iops/subgroup-vanishing-quotient.md)

## Sources

- Liam Eagen, Dario Fiore, Ariel Gabizon, "cq: Cached Quotients for Fast Lookups", IACR ePrint 2022/1763 (2022).
