# Hoeffding's bound for sampling without replacement

Let $s$ be a nonempty finite set, let $R > 0$ and $c : s \to [0, R]$, let $n \in \mathbb{N}$ and
$t \ge 0$, and put $\bar c = \frac{1}{|s|} \sum_{i \in s} c_i$. Then the number of $n$-element
subsets $S \subseteq s$ with

$$n \bar c + t n R \le \sum_{i \in S} c_i$$

is at most $e^{-2 n t^2} \binom{|s|}{n}$. The cases $n = 0$ and $|s| < n$ are included.
