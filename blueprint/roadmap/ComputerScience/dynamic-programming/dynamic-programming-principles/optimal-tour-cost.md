# Optimal tour cost

Let $d$ be a cost function on a finite set of cities with values in a
linearly ordered additive commutative monoid $R$. The optimal tour cost is the minimum, in
$R \cup \{\top\}$, of $d(x_1, x_2) + \dots + d(x_{n-1}, x_n) + d(x_n, x_1)$ over all lists
$[x_1, \dots, x_n]$ that contain every city exactly once: the cheapest closed tour that visits
each city once and returns to its first city. (With no cities, the empty tour costs $0$.)
