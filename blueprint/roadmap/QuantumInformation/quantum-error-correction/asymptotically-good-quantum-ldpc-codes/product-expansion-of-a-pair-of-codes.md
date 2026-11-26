# Product-expansion of a pair of codes

A pair of codes $(C_1, C_2)$ with $C_i \subseteq \mathbb{F}_2^{n_i}$ is *$\rho$-product-expanding* if every $x \in C_1 \boxplus C_2$ admits a decomposition $x = a + b$ with $a \in C_1 \otimes \mathbb{F}_2^{n_2}$ and $b \in \mathbb{F}_2^{n_1} \otimes C_2$ such that

$$
\rho \left( n_2\, |a|_{\mathrm{col}} + n_1\, |b|_{\mathrm{row}} \right) \le |x| ,
$$

where $|a|_{\mathrm{col}}$ is the number of nonzero columns of $a$ and $|b|_{\mathrm{row}}$ the number of nonzero rows of $b$.

## Depends on

- [Tensor codes and dual tensor codes](tensor-codes-and-dual-tensor-codes.md)

## Sources

- Gleb Kalachev, Pavel Panteleev, "Two-sided robustly testable codes", arXiv:2206.09973 (2022).
- Pavel Panteleev, Gleb Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022); arXiv:2111.03654.
