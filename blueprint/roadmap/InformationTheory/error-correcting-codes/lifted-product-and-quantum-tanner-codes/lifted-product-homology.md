# Künneth-type dimension formula for lifted product codes

Let $G$ be a finite group, $R = \mathbb{F}_2[G]$, and let $A \in R^{m_A \times n_A}$ and $B \in R^{m_B \times n_B}$ define two-term chain complexes $\mathcal{A} : R^{n_A} \xrightarrow{A} R^{m_A}$ of right $R$-modules and $\mathcal{B} : R^{n_B} \xrightarrow{B} R^{m_B}$ of left $R$-modules. The lifted product code $\mathrm{LP}(A, B)$ is the CSS code of the tensor complex $\mathcal{A} \otimes_R \mathcal{B}$, with its $n = |G|(n_A m_B + m_A n_B)$ qubits in degree $1$. Its middle homology $H_1(\mathcal{A} \otimes_R \mathcal{B}) = \ker \partial_1 / \operatorname{im} \partial_2$ is the $\mathbb{F}_2$-space of logical operators of one type (logical classes modulo stabilizers), not the code space, and the number of logical qubits is

$$
k = \dim_{\mathbb{F}_2} H_1(\mathcal{A} \otimes_R \mathcal{B}).
$$

The code space itself is a $2^k$-dimensional subspace of $(\mathbb{C}^2)^{\otimes n}$. When $G$ is trivial this reduces to the Künneth formula $k = \dim H_0(\mathcal{A})\dim H_1(\mathcal{B}) + \dim H_1(\mathcal{A})\dim H_0(\mathcal{B})$ of the hypergraph product; in general $k = n - \operatorname{rank} H_X - \operatorname{rank} H_Z \ge |G|(n_A m_B + m_A n_B - n_A n_B - m_A m_B)$.

## Proof sketch

The lifted product is by definition the CSS code with $H_X = \partial_1$ and $H_Z = \partial_2^{*}$ on the degree-$1$ term, so its logical $X$-type operators modulo stabilizers form $\ker \partial_1 / \operatorname{im} \partial_2 = H_1$, and $k = \dim H_1 = n - \operatorname{rank}\partial_1 - \operatorname{rank}\partial_2$. The rank lower bound is the Euler characteristic of the three-term complex: the boundary map out of degree $2$, whose domain $R^{n_A n_B}$ has $\mathbb{F}_2$-dimension $|G| n_A n_B$, has rank at most that, and the boundary map into degree $0$ has rank at most $|G| m_A m_B$. These counts are for $\mathcal{A} \otimes_R \mathcal{B}$; the product $\mathcal{A} \otimes_R \mathcal{B}^{*}$ with the dual complex of $\mathcal{B}$ has $|G|(n_A n_B + m_A m_B)$ qubits and the corresponding bound with $n_B$ and $m_B$ exchanged.

## Depends on

- [Lifted product codes over group algebras](../../../QuantumInformation/quantum-error-correction/homological-quantum-ldpc-codes/lifted-product-codes-over-group-algebras.md)

## Sources

- P. Panteleev, G. Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022), arXiv:2111.03654, Section 1 and Appendix B.
- N. P. Breuckmann, J. N. Eberhardt, "Balanced product quantum codes", IEEE Transactions on Information Theory 67 (2021) 6653-6674, arXiv:2012.09271.
