# Combinatorial Nullstellensatz, Theorem 1.1

Let $F$ be a field, $\sigma$ a finite index set, $f \in F[x_i : i \in \sigma]$, and for each
$i \in \sigma$ let $S_i \subseteq F$ be a nonempty finite set and

$$g_i = \prod_{s \in S_i} (x_i - s).$$

If $f(x) = 0$ for every $x \in \prod_{i} S_i$, then there are polynomials $h_i$ ($i \in \sigma$)
such that

$$f = \sum_{i \in \sigma} h_i g_i,$$

and for every $i$ either $h_i = 0$ or $\deg h_i + \deg g_i \le \deg f$, where $\deg$ is the total
degree. Alon writes the bound as $\deg h_i \le \deg f - \deg g_i$, which is the same condition for
$h_i \ne 0$. Alon also shows that the $h_i$ can be taken with coefficients in any subring containing the coefficients of $f$ and the $g_i$.

## Sources

- Noga Alon, "Combinatorial Nullstellensatz", *Combin. Probab. Comput.* 8 (1999) 7–29, Theorem 1.1.
