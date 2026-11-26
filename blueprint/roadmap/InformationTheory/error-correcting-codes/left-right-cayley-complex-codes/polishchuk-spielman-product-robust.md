# Robust testability of products of Reed-Solomon codes

Let $C = \mathrm{RS}_q[n, k]$ be a Reed-Solomon code over $\mathbb{F}_q$ with $k \le n/4$. Then the tensor code $C \otimes C$ is robustly testable with an absolute constant: for every $w \in \mathbb{F}_q^{n \times n}$,

$$
\mathbb{E}_{i}\, \frac{\operatorname{dist}(w_{i,\cdot}, C)}{n} + \mathbb{E}_{j}\, \frac{\operatorname{dist}(w_{\cdot,j}, C)}{n} \ge \Omega\bigl(\operatorname{dist}(w, C \otimes C)/n^2\bigr).
$$

This bivariate low-degree test underlies the classical constructions of nearly linear size PCPs.

## Proof sketch

Decode each row and column to the nearest Reed-Solomon codeword; the decoded rows and columns form a bivariate function of individual degree less than $k$ on a large fraction of the grid. A bivariate analogue of the Berlekamp-Welch error locator polynomial shows that this function agrees with a single tensor codeword on all but an $O(\text{robust distance})$ fraction of points when $k \le n/4$.

## Depends on

- [Agreement testability and robustness of tensor codes](agreement-testability-tensor.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Sources

- A. Polishchuk, D. A. Spielman, "Nearly-linear size holographic proofs", STOC (1994).
- E. Ben-Sasson, M. Sudan, "Robust locally testable codes and products of codes", Random Structures & Algorithms 28 (2006) 387-402.
