# Higher order MDS codes MDS(l)

Let $C$ be a linear $[n, k]$ code with generator matrix $G \in \mathbb{F}^{k \times n}$, and for $A \subseteq [n]$ let $G_A \le \mathbb{F}^k$ be the span of the columns of $G$ indexed by $A$. The code is *$\mathrm{MDS}(\ell)$* (higher order MDS of order $\ell$) if for all $A_1, \dots, A_\ell \subseteq [n]$,

$$
\dim\big(G_{A_1} \cap \cdots \cap G_{A_\ell}\big) = \dim\big(W_{A_1} \cap \cdots \cap W_{A_\ell}\big),
$$

where $W$ is a generic $k \times n$ matrix (with algebraically independent entries over $\mathbb{F}$). $\mathrm{MDS}(2)$ is equivalent to MDS, and $\mathrm{MDS}(\ell)$ implies $\mathrm{MDS}(\ell')$ for $\ell' \le \ell$.

## Depends on

- [Linear code](../linear-codes/linear-code.md)
- [Reed-Solomon codes meet the Singleton bound](../reed-solomon-codes/min-dist-code-eq-singleton.md)

## Sources

- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Lower bounds for maximally recoverable tensor codes and higher order MDS codes", IEEE Transactions on Information Theory 68(11) (2022); arXiv:2107.10822.
- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256.
