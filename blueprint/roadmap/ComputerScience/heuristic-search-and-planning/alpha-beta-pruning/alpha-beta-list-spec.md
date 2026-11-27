# Correctness of the alpha-beta scan

Let $p$ be the player to move, $ts$ a list of game
trees with values in a bounded linear order, and $a \le b$. Let $r$ be the value returned by the
alpha-beta scan of $ts$ for $p$ with window $[a, b]$, and let $m$ be the best value for $p$ among
$ts$: the maximum of the minimax values of the trees in $ts$ for the minimizer ($\bot$ if $ts$ is
empty) when $p$ is the maximizer, and the minimum of their minimax values for the maximizer
($\top$ if $ts$ is empty) when $p$ is the minimizer. Then $\max(a, \min(b, r)) =
\max(a, \min(b, m))$.
