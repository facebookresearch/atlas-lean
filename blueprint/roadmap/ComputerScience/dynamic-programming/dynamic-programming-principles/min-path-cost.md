# Cheapest path through a set of cities

Let $d$ be a cost function on the cities with
values in a linearly ordered additive commutative monoid $R$. For cities $s$, $j$ and a finite set
$S$ of cities, $C(S, j)$ is the minimum, in $R \cup \{\top\}$, of
$d(s, x_1) + d(x_1, x_2) + \dots + d(x_{k-1}, x_k)$ over all lists $[x_1, \dots, x_k]$ such that
$s, x_1, \dots, x_k$ is a path from $s$ to $j$ that visits exactly the cities of $S$, each once;
it is $\top$ when there is no such path. Such a list orders $S \setminus \{s\}$, so there are
finitely many.
