# Product-expansion of a pair of codes

A pair of codes $(C_1, C_2)$ with $C_i \subseteq \mathbb{F}_2^{n_i}$ is *$\rho$-product-expanding* if every $x \in C_1 \boxplus C_2 = C_1 \otimes \mathbb{F}_2^{n_2} + \mathbb{F}_2^{n_1} \otimes C_2$ admits a decomposition $x = a + b$ with $a \in C_1 \otimes \mathbb{F}_2^{n_2}$ and $b \in \mathbb{F}_2^{n_1} \otimes C_2$ such that

$$
\rho \left( n_1\, |a|_{\mathrm{col}} + n_2\, |b|_{\mathrm{row}} \right) \le |x| ,
$$

where, viewing words as $n_1 \times n_2$ matrices, $|a|_{\mathrm{col}}$ is the number of nonzero columns of $a$ (each a codeword of $C_1$, of length $n_1$) and $|b|_{\mathrm{row}}$ the number of nonzero rows of $b$ (each a codeword of $C_2$, of length $n_2$). Each nonzero column or row is thus weighted by its length. For $n_1 = n_2 = \Delta$ this says that $(C_1, C_2)$ is $\rho\Delta$-robust in the sense of Dinur, Hsieh, Lin and Vidick, which is equivalent to $\rho$-agreement testability of $C_1 \otimes C_2$. A pair is *two-sided* product-expanding when both $(C_1, C_2)$ and the pair of duals $(C_1^{\perp}, C_2^{\perp})$ are product-expanding.

## Depends on

- [Tensor codes and dual tensor codes](tensor-codes-and-dual-tensor-codes.md)

## Sources

- Irit Dinur, Min-Hsiu Hsieh, Ting-Chun Lin, Thomas Vidick, "Good quantum LDPC codes with linear time decoders", STOC (2023); arXiv:2206.07750, Section 2.6, Definitions 2.7-2.9.
- Irit Dinur, Shai Evra, Ron Livne, Alexander Lubotzky, Shahar Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022); arXiv:2111.04808, Definition 2.8 and Lemma 2.9.
