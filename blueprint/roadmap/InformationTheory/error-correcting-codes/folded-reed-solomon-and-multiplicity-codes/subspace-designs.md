# Subspace designs

A collection $H_1, \dots, H_M$ of $\mathbb{F}_q$-subspaces of $\mathbb{F}_q^{k}$ is an *$(r, A)$-subspace design* if every $r$-dimensional subspace $W \le \mathbb{F}_q^k$ satisfies

$$
\sum_{i=1}^{M} \dim(H_i \cap W) \le A .
$$

For the message space $\mathbb{F}_q[x]_{<k}$ of a folded Reed-Solomon code, the subspaces $H_i = \{f : f(\gamma^{j}\alpha_i) = 0 \text{ for } 0 \le j < s\}$ form an $(r, A)$-subspace design with $A = \frac{r(k-1)}{s - r + 1}$ for every $r \le s$, by counting zeros of folded Wronskians (Guruswami-Kopparty).

## Depends on

- [Folded Wronskian criterion for linear independence](folded-wronskian-criterion-for-linear-independence.md)

## Sources

- Venkatesan Guruswami, Swastik Kopparty, "Explicit subspace designs", Combinatorica 36(2) (2016), FOCS (2013).
