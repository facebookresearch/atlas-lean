# Union bound

Let $\mu$ be a distribution on a set $A$, $f : A \to \{0, 1\}$ and $g_0, \dots, g_{q-1} : A \to \{0, 1\}$.
If for every $a$ with $f(a) = 1$ there is a $j < q$ with $g_j(a) = 1$, then

$$\Pr_{a \sim \mu}[f(a) = 1] \le \sum_{j < q} \Pr_{a \sim \mu}[g_j(a) = 1].$$
