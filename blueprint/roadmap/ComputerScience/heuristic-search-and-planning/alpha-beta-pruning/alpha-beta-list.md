# Alpha-beta scan of the children

Given the player $p$ to move, values $a$ and $b$ in a
linear order and a list of game trees (the children of a position), the scan runs alpha-beta
pruning for the other player on the children in order, each time with the current bounds $a$ and
$b$. The maximizer replaces $a$ by $\max(a, v)$, where $v$ is the child's returned value, and
stops as soon as $b \le a$, returning the new $a$; if it never stops early it returns the final
$a$ ($a$ itself for an empty list). The minimizer replaces $b$ by $\min(b, v)$ and stops as soon
as $b \le a$, returning the new $b$; if it never stops early it returns the final $b$ ($b$ itself
for an empty list). The cost of the scan is the total cost of the children it evaluates.
