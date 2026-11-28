# Maximizer's scan when every child fails low

Let $a < b$, let $u_1, \dots, u_m$ be the children of a maximizer node, and suppose every child
has minimizer value at most $a$ and costs exactly $c$ leaf evaluations under alpha-beta with
window $(a, b)$. Then the maximizer's scan keeps the bound $a$, never cuts off, and evaluates
exactly $m c$ leaves.
