# Spoof totient

Let $F$ be a finite multiset of pairs $(x_i, a_i)$ of natural numbers,
$i = 1, \dots, r$, viewed as the formal product $x_1^{a_1} \cdots x_r^{a_r}$. The spoof totient
of $F$ is the integer $\tilde\varphi(F) = \prod_{i=1}^{r} (x_i^{a_i} - x_i^{a_i - 1})$, where
the exponent $a_i - 1$ is truncated at $0$, so a pair with $a_i = 0$ contributes the factor $0$.

## Sources

- Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026), Article A33, Definition 3.
