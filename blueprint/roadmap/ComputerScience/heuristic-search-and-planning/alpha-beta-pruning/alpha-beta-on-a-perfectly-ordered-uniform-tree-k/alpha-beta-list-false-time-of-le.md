# Minimizer's scan when every child fails high

Let $a < b$, let $u_1, \dots, u_m$ be the children of a minimizer node, and suppose every child
has maximizer value at least $b$ and costs exactly $c$ leaf evaluations under alpha-beta with
window $(a, b)$. Then the minimizer's scan keeps the bound $b$, never cuts off, and evaluates
exactly $m c$ leaves.
