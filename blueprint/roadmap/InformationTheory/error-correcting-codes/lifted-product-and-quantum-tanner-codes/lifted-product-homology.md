# Künneth-type dimension formula for lifted product codes

Let $G$ be a finite group, $R = \mathbb{F}_2[G]$, and let $A, B$ be matrices over $R$ defining two-term chain complexes $\mathcal{A} : R^{n_A} \xrightarrow{A} R^{m_A}$ and $\mathcal{B} : R^{n_B} \xrightarrow{B} R^{m_B}$ of left and right $R$-modules respectively. The lifted product code $\mathrm{LP}(A, B)$ is the middle homology of the tensor complex $\mathcal{A} \otimes_R \mathcal{B}$, and its number of logical qubits is

$$
k = \dim_{\mathbb{F}_2} H_1(\mathcal{A} \otimes_R \mathcal{B}).
$$

When $G$ is trivial this reduces to the Künneth formula $k = \dim H_0(\mathcal{A})\dim H_1(\mathcal{B}) + \dim H_1(\mathcal{A})\dim H_0(\mathcal{B})$ of the hypergraph product; in general $k = n - \operatorname{rank} H_X - \operatorname{rank} H_Z \ge |G|(n_A m_B + m_A n_B - n_A n_B - m_A m_B)$, where $n = |G|(n_A m_B + m_A n_B)$ is the number of qubits.

## Proof sketch

The lifted product is by definition the complex $\mathcal{A} \otimes_R \mathcal{B}$ with qubits in degree $1$, so its CSS code space has the stated dimension. The rank lower bound is the Euler characteristic of the three-term complex, since the boundary map out of degree $2$ has rank at most $|G| n_A n_B$ and the boundary map into degree $0$ has rank at most $|G| m_A m_B$.

## Depends on

- [Lifted product codes over group algebras](../../../QuantumInformation/quantum-error-correction/homological-quantum-ldpc-codes/lifted-product-codes-over-group-algebras.md)

## Sources

- P. Panteleev, G. Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022), arXiv:2111.03654.
- N. P. Breuckmann, J. N. Eberhardt, "Balanced product quantum codes", IEEE Transactions on Information Theory 67 (2021) 6653-6674, arXiv:2012.09271.
