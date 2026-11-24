# Generalized hockey stick theorem as a signed sum over compositions

For all natural numbers $k, n, r$,

$$\sum_{i=0}^{k} \binom{(r+1)i + n}{i} = \sum_{\alpha \in \mathcal{C}(k, r)} \operatorname{sgn}(\alpha) \left(\prod_{j=1}^{\ell(\alpha)} \binom{r}{\alpha_j - 1}\right) \binom{(r+1)k + n + 1 - |\alpha| + \ell(\alpha)}{k - |\alpha|},$$

computed in the integers, where $\mathcal{C}(k, r)$ is the set of compositions $\alpha = (\alpha_1, \dots, \alpha_{\ell(\alpha)})$, including the empty one, with every part in $\{2, \dots, r + 1\}$ and size $|\alpha| \le k$, and $\operatorname{sgn}(\alpha) = (-1)^{|\alpha| - \ell(\alpha)}$. For $r = 0$ only the empty composition occurs and the identity is the classical hockey stick identity $\sum_{i=0}^{k} \binom{i + n}{i} = \binom{k + n + 1}{k}$.

## Sources

- Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, J. Integer Seq. 28 (2025), Article 25.7.7, Corollary 13, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Weselcouch/wesel8.html>.
