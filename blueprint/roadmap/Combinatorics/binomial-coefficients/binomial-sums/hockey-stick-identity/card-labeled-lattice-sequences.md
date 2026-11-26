# Number of labeled lattice sequences of a given shape

Let $k, n, r$ be natural numbers and let $\alpha = (\alpha_1, \dots, \alpha_\ell) \in \mathcal{C}(k, r)$ be a composition with parts in $\{2, \dots, r+1\}$ and size $|\alpha| \le k$. The labeled lattice sequences $(\lambda, L)$ of type $(k, n, r)$ and shape $\alpha$ are the pairs with $\lambda \in \Lambda(\alpha, r)$ and $L \in \mathcal{L}(rk + n + 1 + \ell, k - |\alpha|)$, and their number is

$$|\Lambda(\alpha, r)| \cdot |\mathcal{L}(rk + n + 1 + \ell, k - |\alpha|)| = \left(\prod_{j=1}^{\ell} \binom{r}{\alpha_j - 1}\right) \binom{(r+1)k + n + 1 - |\alpha| + \ell}{k - |\alpha|}.$$

## Sources

- Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, J. Integer Seq. 28 (2025), Article 25.7.7, Proposition 11, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Weselcouch/wesel8.html>.
