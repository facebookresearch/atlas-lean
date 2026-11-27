# Identification of a causal effect when some instruments are invalid

Let $Z$ be an $n \times L$ matrix of candidate instruments (e.g. genotypes), $D$ the exposure and $Y$ the outcome, related by the linear model

$$Y = Z\alpha^* + D\beta^* + \varepsilon, \qquad \mathbb E(\varepsilon \mid Z) = 0,$$

where $\beta^*$ is the causal effect and instrument $j$ is **valid** if $\alpha^*_j = 0$ and **invalid** otherwise, so that the set of invalid instruments is $\operatorname{supp}(\alpha^*)$ with $s = |\operatorname{supp}(\alpha^*)|$. Assume (a) $\mathbb E(Z^\top Z)$ has full rank, and (b) writing $\mathbb E(Z^\top D) = \mathbb E(Z^\top Z)\gamma^*$, every $\gamma^*_j \ne 0$. With $\Gamma^* = \mathbb E(Z^\top Z)^{-1}\mathbb E(Z^\top Y)$, the moment condition $\mathbb E\big(Z^\top(Y - Z\alpha^* - D\beta^*)\big) = 0$ is equivalent to

$$\Gamma^* = \alpha^* + \gamma^* \beta^* .$$

Suppose $s < U$ for a known bound $U \in \{1, \dots, L\}$. Consider all sets $C_m \subseteq \{1, \dots, L\}$ $(m = 1, \dots, M)$ of size $L - U + 1$ for which there is a constant $q_m$ with $\gamma^*_j q_m = \Gamma^*_j$ for all $j \in C_m$.

**Theorem (consistency criterion).** There is a unique solution $(\alpha^*, \beta^*)$ of $\Gamma^* = \alpha^* + \gamma^*\beta^*$ with $\|\alpha^*\|_0 < U$ if and only if $q_m = q_{m'}$ for all $m, m'$.

**Corollary (majority rule).** If $U \le L/2$, so that fewer than half of the instruments are invalid, the solution is always unique.

Moreover, $\beta^*$ is unique exactly when $\alpha^*$ is unique.

## Depends on

- [Linear moment model for instrumental variables](linear-moment-model.md)
- [Ratio estimate of a single SNP](ratio-estimate.md)

## Expansion

If the valid set were known, $\gamma^*_j\beta^* = \Gamma^*_j$ on it would pin down $\beta^*$ from one valid instrument. Without that knowledge, each subset of size $L - U + 1$ on which the ratios $\Gamma^*_j/\gamma^*_j$ agree proposes a value $q_m$ of $\beta^*$; non-identification occurs exactly when two such subsets propose different values. For instance, $\gamma^* = (1,2,3,4)$ and $\Gamma^* = (1,2,6,8)$ with $U = 3$ give $C_1 = \{1,2\}$, $C_2 = \{3,4\}$ with $q_1 = 1 \ne q_2 = 2$. When $U \le L/2$, any two sets $C_m, C_{m'}$ have size $L - U + 1 > L/2$, so they share some index $j$; then $\gamma^*_j q_m = \Gamma^*_j = \gamma^*_j q_{m'}$ with $\gamma^*_j \ne 0$ forces $q_m = q_{m'}$. This is Theorem 1 and Corollary 1 of Section 3.1.

## Sources

- H. Kang, A. Zhang, T. T. Cai, D. S. Small, "Instrumental Variables Estimation With Some Invalid Instruments and its Application to Mendelian Randomization", Journal of the American Statistical Association 111 (2016), 132–144, <https://doi.org/10.1080/01621459.2014.994705>.
