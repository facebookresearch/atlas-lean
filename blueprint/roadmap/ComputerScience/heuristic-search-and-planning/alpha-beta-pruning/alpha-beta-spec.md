# Alpha-beta is correct

Let $t$ be a game tree with values in a bounded linear order, $p$ the player to move and
$a \le b$ values. Let $r$ be the value returned by [alpha-beta pruning](alpha-beta.md) on $t$ for
$p$ with window $[a, b]$ and $v$ the [minimax value](minimax.md) of $t$ for $p$. Then $r$ and $v$
agree after clamping both to the window: $\max(a, \min(b, r)) = \max(a, \min(b, v))$. This is
Theorem 1 of Knuth and Moore (1975).
