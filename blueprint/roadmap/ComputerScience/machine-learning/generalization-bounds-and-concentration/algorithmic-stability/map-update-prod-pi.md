# Replace-one sampling preserves the law of an i.i.d. sample

Let $\nu$ be a probability measure on $\mathcal{Z}$, let $S = (z_1, \dots, z_n) \sim \nu^{\otimes n}$ and $z \sim \nu$ be independent, and let $S^{(i, z)}$ be the sample $S$ with its $i$-th example replaced by $z$. Then $S^{(i, z)}$ has law $\nu^{\otimes n}$: the image of $\nu^{\otimes n} \otimes \nu$ under $(S, z) \mapsto S^{(i, z)}$ is $\nu^{\otimes n}$.

Proof: on a box $\prod_j B_j$, the preimage is $\big(\prod_{j \ne i} B_j \times \mathcal{Z}\big) \times B_i$, of measure $\prod_{j \ne i} \nu(B_j) \cdot \nu(\mathcal{Z}) \cdot \nu(B_i) = \prod_j \nu(B_j)$, and boxes determine a product measure.

This is the exchange step of the stability argument: the loss of $A(S)$ at the training example $z_i$ has the same law as the loss of $A(S^{(i, z)})$ at the fresh example $z$.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, proof of Theorem 2.2 (the sample $S^{(i)}$ built from two independent samples $S$ and $S'$).
