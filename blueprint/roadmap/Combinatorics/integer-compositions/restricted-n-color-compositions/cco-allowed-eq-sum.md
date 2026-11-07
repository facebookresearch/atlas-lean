# Double-sum formula for n-color compositions with two consecutive colors

Let $b \ge 1$
and $n \ge 1$ be natural numbers, and let $\operatorname{cco}_{b,b+1}(n)$ be the number of
$n$-color compositions of $n$ in which every part has color $b$ or $b+1$. Then

$$\operatorname{cco}_{b,b+1}(n) = \sum_{m=1}^{n} \sum_{i=0}^{n-bm}
\binom{i+m-1}{m-1} \binom{m}{n-bm-i},$$

where the upper limit $n - bm$ is read as $0$ when $bm > n$, and every term with $bm + i > n$
is $0$.

## Sources

- Brian Hopkins and Hua Wang, "Allowing or Prohibiting Two Consecutive Colors in `n`-Color Compositions", Proposition 1.
