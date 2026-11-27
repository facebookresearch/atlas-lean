# GM-MDS theorem (Lovett; Yildiz-Hassibi)

Let $(Z_1, \dots, Z_k)$ be a zero pattern for $k \times n$ matrices satisfying the GM-MDS condition, and let $\mathbb{F}_q$ have size $q \ge n + k - 1$. Then there exist distinct $\alpha_1, \dots, \alpha_n \in \mathbb{F}_q$ and a generator matrix of the Reed-Solomon code $\mathrm{RS}_k(\alpha_1, \dots, \alpha_n)$ attaining the pattern. Equivalently, generator matrices of Reed-Solomon codes with generic evaluation points attain every zero pattern attainable by any MDS code.

## Proof sketch

Row $i$ of an RS generator matrix attaining the pattern is the evaluation vector of a polynomial of degree less than $k$ vanishing on $\{\alpha_j : j \in Z_i\}$, i.e. a multiple of $\prod_{j \in Z_i}(x - \alpha_j)$. One must show that the $k$ spaces of such polynomials can be chosen with linearly independent representatives; this reduces to non-vanishing of a determinant polynomial in the $\alpha_j$. Lovett proves non-vanishing by an inductive argument on the pattern (removing or merging sets) using a degree-reduction lemma; Yildiz-Hassibi give an independent proof, and the degree bound yields the field size $n + k - 1$.

## Depends on

- [Zero patterns and the GM-MDS condition](gm-mds-zero-patterns.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Sources

- Shachar Lovett, "MDS matrices over small fields: a proof of the GM-MDS conjecture", FOCS (2018); arXiv:1803.02523.
- Hikmet Yildiz, Babak Hassibi, "Optimum linear codes with support-constrained generator matrices over small fields", IEEE Transactions on Information Theory 65(12) (2019); arXiv:1803.03752.
