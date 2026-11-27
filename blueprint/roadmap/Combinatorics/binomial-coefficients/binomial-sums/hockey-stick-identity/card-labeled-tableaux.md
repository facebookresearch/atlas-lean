# Number of labeled tableaux of a given shape

For every finite list $\alpha = (\alpha_1, \dots, \alpha_\ell)$ of natural numbers and every natural number $r$, the number of labeled tableaux of shape $\alpha$ with labels in $\{0, \dots, r-1\}$ (tuples of subsets $S_j$ of $\{0, \dots, r-1\}$ with $|S_j| = \alpha_j - 1$) is

$$|\Lambda(\alpha, r)| = \prod_{j=1}^{\ell} \binom{r}{\alpha_j - 1},$$

with truncated subtraction ($\alpha_j - 1 = 0$ when $\alpha_j = 0$); the empty product, for $\alpha = \emptyset$, is $1$.

## Sources

- Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, J. Integer Seq. 28 (2025), Article 25.7.7, Proposition 4, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Weselcouch/wesel8.html>.
