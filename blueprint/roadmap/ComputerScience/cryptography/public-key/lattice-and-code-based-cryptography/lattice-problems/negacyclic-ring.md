# The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$

Let $R$ be a commutative ring and $n \ge 1$. The *negacyclic ring* of degree $n$ over $R$ is the quotient $R[X]/(X^n + 1)$. Every element has a unique representative $a = \sum_{i=0}^{n-1} a_i X^i$, so it is identified with its coefficient vector $(a_0, \dots, a_{n-1}) \in R^n$. Since $X^n \equiv -1$, the product $c = a \cdot b$ has coefficients

$$
c_k = \sum_{i + j = k} a_i b_j \;-\; \sum_{i + j = k + n} a_i b_j \qquad (0 \le k < n),
$$

equivalently $c = \mathrm{rot}(a)\, b$, where the *negacyclic rotation matrix* $\mathrm{rot}(a) \in R^{n \times n}$ has $j$-th column the coefficient vector of $X^j a$. In lattice cryptography one takes $R = \mathbb{Z}_q$ and writes $R_q = \mathbb{Z}_q[X]/(X^n+1)$, usually with $n$ a power of two so that $X^n + 1$ is the $2n$-th cyclotomic polynomial. A $d \times k$ *module matrix* $\mathbf{A} \in R_q^{d \times k}$ acts on $R_q^k$ by $(\mathbf{A}\mathbf{z})_i = \sum_j A_{ij} z_j$, and replacing every entry by its rotation matrix gives the *expanded* matrix $\mathrm{rot}(\mathbf{A}) \in \mathbb{Z}_q^{dn \times kn}$ with $\mathrm{flat}(\mathbf{A}\mathbf{z}) = \mathrm{rot}(\mathbf{A})\,\mathrm{flat}(\mathbf{z})$ for the coefficient flattening $\mathrm{flat}$.

## Sources

- Vadim Lyubashevsky, Chris Peikert and Oded Regev, "On Ideal Lattices and Learning with Errors over Rings", Advances in Cryptology – EUROCRYPT 2010, 2010.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
