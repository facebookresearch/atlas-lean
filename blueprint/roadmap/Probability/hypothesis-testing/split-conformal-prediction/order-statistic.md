# Order statistic with multiplicity

Let $\iota$ be a finite set, $f : \iota \to \mathbb{R}$ and $k \in \mathbb{N}$. The $k$-th smallest value of $f$, counted with multiplicity, is

$$f_{(k)} = \min\{f(i) : \#\{j : f(j) \le f(i)\} \ge k\},$$

the least value $f(i)$ such that at least $k$ indices $j$ satisfy $f(j) \le f(i)$, and $+\infty$ when no value qualifies; for $k \ge 1$ this happens exactly when $k > |\iota|$. For $k = 0$ the value is the minimum of $f$ (and $+\infty$ if $\iota$ is empty) by convention; the results below assume $k \ge 1$.
