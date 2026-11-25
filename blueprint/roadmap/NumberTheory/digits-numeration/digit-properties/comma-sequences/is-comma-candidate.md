# Comma candidate digits

Let $b$ and $n$ be natural numbers and let $y$ be a digit with
$0 \le y < b$. Put $m = n + b\,(n \bmod b) + y$, where $n \bmod b$ is the remainder of $n$ on
division by $b$. Then $y$ is a comma candidate for $n$ in base $b$ if $m > 0$ and the most
significant base-$b$ digit of $m$ equals $y$.

For such a candidate $y$ in base $b \ge 2$, the difference $m - n = b\,(n \bmod b) + y$ is
written with the base-$b$ digits $n \bmod b$ and $y$: the last digit of $n$ followed by the
leading digit of $m$.
