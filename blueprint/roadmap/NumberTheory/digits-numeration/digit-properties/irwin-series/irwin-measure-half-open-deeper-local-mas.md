# Local structure of the Irwin measures on half-open intervals

Let $b > 1$ and $d < b$ be
natural numbers, and for each natural number $k$ let $\mu_k$ be the Irwin measure of base $b$ and
digit $d$ with index $k$. Let $x \in [0, 1)$ have base-$b$ depth $l$, that is, $l$ is the least
natural number such that $b^l x$ is an integer; let $X$ be a string of $l$ base-$b$ digits, read
most significant digit first, whose value $n(X)$ satisfies $n(X)/b^l = x$; and let $j$ be the
number of occurrences of $d$ in $X$. Let $l' \ge l$ be a natural number, put $j' = j$ if $d > 0$
and $j' = j + l' - l$ if $d = 0$, and let $k \ge j'$ be a natural number. Suppose moreover that
$l' = l$ or $j < k$ when $d > 0$. Then for every set $U \subseteq [x, x + b^{-l'})$, as real
numbers, $\mu_k(U) = b^{-l'} \mu_{k-j'}(b^{l'} U - b^{l'} x)$, where $b^{l'} U - b^{l'} x$ is the
image of $U$ under $y \mapsto b^{l'} y - b^{l'} x$.

The extra condition is needed because of the atom at $x$, which carries the strings $X 0^r$:
for $b = 2$, $d = 1$, $x = 0$, $l = j = k = 0$, $l' = 1$ and $U = \{0\}$ the left side is $2$
and the right side is $1$. The source states the lemma without it.

## Sources

- Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Lemma 3.
