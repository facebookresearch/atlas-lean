# Rough numbers other than $1$ lie in Mathlib's rough numbers up to a bound

Let $n$,
$N$ and $k$ be natural numbers. If $n$ is $k$-rough, $n \le N$ and $n \ne 1$, then $n$ belongs
to the set of natural numbers $m$ with $1 \le m \le N$ that are not $(k+1)$-smooth, where $m$ is
$(k+1)$-smooth when $m > 0$ and every prime factor of $m$ is less than $k + 1$; for $m \ge 1$,
not being $(k+1)$-smooth means having a prime factor $p \ge k + 1$.

This set is Mathlib's set of rough numbers up to $N$ at bound $k + 1$. It asks only for some
prime factor $p \ge k + 1$, while $k$-roughness asks that every prime factor exceed $k$.
