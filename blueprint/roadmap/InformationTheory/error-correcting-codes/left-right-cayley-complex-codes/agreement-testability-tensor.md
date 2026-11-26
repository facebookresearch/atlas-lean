# Agreement testability and robustness of tensor codes

Let $C_1 \subseteq \mathbb{F}_2^{n_1}$ and $C_2 \subseteq \mathbb{F}_2^{n_2}$ be linear codes. For a pair $(c, r)$ consisting of a matrix $c$ whose columns lie in $C_1$ and a matrix $r$ whose rows lie in $C_2$, both in $\mathbb{F}_2^{n_1 \times n_2}$, the tensor code $C_1 \otimes C_2$ is **$\kappa$-agreement testable** if

$$
\frac{|c - r|}{n_1 n_2} \ge \kappa \cdot \min_{w \in C_1 \otimes C_2} \Bigl( \frac{|c - w|}{n_1 n_2} + \frac{|r - w|}{n_1 n_2} \Bigr),
$$

where $|\cdot|$ is Hamming weight. Agreement testability is equivalent, up to constants, to **robust testability** of the tensor code: the expected distance of a random row or column view from $C_2$ or $C_1$ bounds the distance of the word from $C_1 \otimes C_2$. A pair is **two-sided robust** if, in addition, the same holds for the dual tensor code $C_1^{\perp} \otimes \mathbb{F}_2^{n_2} + \mathbb{F}_2^{n_1} \otimes C_2^{\perp}$.

## Depends on

- [Minimum distance of a binary code](../locally-testable-codes/distance.md)

## Sources

- E. Ben-Sasson, M. Sudan, "Robust locally testable codes and products of codes", Random Structures & Algorithms 28 (2006) 387-402.
- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- G. Kalachev, P. Panteleev, "Two-sided robustly testable codes", arXiv:2206.09973 (2022).
