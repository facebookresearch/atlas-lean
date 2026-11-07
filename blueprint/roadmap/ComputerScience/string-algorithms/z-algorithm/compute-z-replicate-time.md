# Z-algorithm cost on a repeated symbol

Let $\alpha$ be a type with a lawful Boolean
equality test, let $a \in \alpha$ and $n \in \mathbb{N}$. The Z-algorithm run on the word $a^n$ has
cost exactly $2(n - 1)$, read as $0$ when $n = 0$, where the cost counts one unit for each visited
position $i \ge 1$ and one unit for each symbol comparison. Thus it makes $n - 1$ visits and
$n - 1$ comparisons.
