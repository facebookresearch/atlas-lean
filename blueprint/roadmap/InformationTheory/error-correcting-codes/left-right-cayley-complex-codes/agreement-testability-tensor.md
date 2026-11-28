# Agreement testability and robustness of tensor codes

Let $C_1 \subseteq \mathbb{F}_2^{n_1}$ and $C_2 \subseteq \mathbb{F}_2^{n_2}$ be linear codes, and view words of length $n_1 n_2$ as $n_1 \times n_2$ matrices, so that $C_1 \otimes C_2$ consists of the matrices whose columns lie in $C_1$ and whose rows lie in $C_2$. The tensor code $C_1 \otimes C_2$ is **$\kappa$-agreement testable** if for every matrix $c$ whose columns lie in $C_1$ and every matrix $r$ whose rows lie in $C_2$ there is $w \in C_1 \otimes C_2$ with

$$
\kappa \left( \frac{\#\{j : c_{\cdot j} \ne w_{\cdot j}\}}{n_2} + \frac{\#\{i : r_{i \cdot} \ne w_{i \cdot}\}}{n_1} \right) \le \frac{|c - r|}{n_1 n_2},
$$

where $|\cdot|$ is Hamming weight. The left side counts the columns of $c$ and the rows of $r$ that must be changed; multiplied by $n_1 n_2$ it weights each changed column by its length $n_1$ and each changed row by its length $n_2$. The tensor code is **$\tau$-robustly testable** if for every $f \in \mathbb{F}_2^{n_1 \times n_2}$,

$$
\tfrac12 \bigl( \mathrm{dist}(f, C_1 \otimes \mathbb{F}_2^{n_2}) + \mathrm{dist}(f, \mathbb{F}_2^{n_1} \otimes C_2) \bigr) \ge \tau \cdot \mathrm{dist}(f, C_1 \otimes C_2)
$$

in relative Hamming distance. When $C_1$ and $C_2$ have positive relative distance the two notions are equivalent up to constants depending on $\kappa$ or $\tau$ and the distances. The pair is **two-sided robust** if, in addition, the tensor product of the duals $C_1^{\perp} \otimes C_2^{\perp}$ is agreement testable.

## Depends on

- [Minimum distance of a binary code](../locally-testable-codes/distance.md)

## Sources

- E. Ben-Sasson, M. Sudan, "Robust locally testable codes and products of codes", Random Structures & Algorithms 28 (2006) 387-402.
- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808, Definitions 2.5 and 2.8 and Lemma 2.9.
- I. Dinur, M.-H. Hsieh, T.-C. Lin, T. Vidick, "Good quantum LDPC codes with linear time decoders", STOC (2023), arXiv:2206.07750, Section 2.6.
