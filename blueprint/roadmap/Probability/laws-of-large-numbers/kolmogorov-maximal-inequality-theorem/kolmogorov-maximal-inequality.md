# Kolmogorov's maximal inequality for finitely-valued variables

Let $\alpha$ be a finite
nonempty set and $n \in \mathbb{N}$. For each $i \in \{0, \dots, n-1\}$ let $p_i$ be a probability
vector on $\alpha$, so $p_i(a) \ge 0$ and $\sum_{a \in \alpha} p_i(a) = 1$, and let
$X_i : \alpha \to \mathbb{R}$ satisfy $\sum_{a \in \alpha} p_i(a) X_i(a) = 0$. Give each
$\omega \in \alpha^n$ the weight $\prod_{i=0}^{n-1} p_i(\omega_i)$, so that the coordinates are
independent with laws $p_i$. Then for every real $\lambda > 0$, the total weight of the $\omega$
for which $\bigl|\sum_{j \le i} X_j(\omega_j)\bigr| \ge \lambda$ for some $i$ is at most
$\lambda^{-2} \sum_{i=0}^{n-1} \sum_{a \in \alpha} p_i(a) X_i(a)^2$.

## Sources

- A. Kolmogoroff, "Über die Summen durch den Zufall bestimmter unabhängiger Größen", Math. Ann. 99 (1928), 309–319, DOI 10.1007/BF01459098.
