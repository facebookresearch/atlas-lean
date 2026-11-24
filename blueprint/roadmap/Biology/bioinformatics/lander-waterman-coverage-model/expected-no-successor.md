# Expected number of no-successor reads

For $G > 0$ and $L \le G$,

$$\sum_{j=1}^{N} \nu_j = N \Bigl(1 - \frac{\max(L - 1, 0)}{G}\Bigr)^{\max(N - 1, 0)},$$

where $\nu_j$ is the [normalized count](normalized-count.md) of the start tuples in which read $j$ has [no successor](no-successor.md). For $L = 0$ the right side is $N$.
