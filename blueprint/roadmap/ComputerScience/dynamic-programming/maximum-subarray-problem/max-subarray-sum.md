# Kadane's algorithm

Let $\alpha$ be a linearly ordered type with an additive monoid
structure. On the empty list, Kadane's algorithm returns no value. On a list
$x_1, x_2, \dots, x_n$ of elements of $\alpha$ with $n \ge 1$, it sets $e = b = x_1$; then for
$i = 2, \dots, n$ in turn it replaces $e$ by $\max(x_i, e + x_i)$ and then $b$ by $\max(b, e)$;
finally it returns $b$. Each of the steps $i = 2, \dots, n$ is charged three operations, and
nothing else is charged.

When $u \le v$ implies $u + w \le v + w$ for all $u, v, w \in \alpha$, after each step $e$ is the
largest sum of a nonempty contiguous run ending at the element just read, and $b$ is the largest
sum of a nonempty contiguous run among the elements read so far.
