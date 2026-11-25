# Packing recurrence for multiple-choice knapsack

Let $\beta$ be a linearly ordered additive commutative monoid, and let $\beta_\bot$ be $\beta$
with a new least element $\bot$ adjoined, with $\bot + x = x + \bot = \bot$. For a list of groups of
knapsack items with values in $\beta$ and a capacity $c \in \mathbb{N}$, the packing recurrence
$P$ takes values in $\beta_\bot$ and is defined by recursion on the groups. With no groups,
$P(c) = 0$ for every $c$. For a first group $G$ followed by the remaining groups $\mathcal{R}$,
$P(G\mathcal{R}, c)$ is the maximum, over the items $a \in G$ with weight $w(a) \le c$, of
$v(a) + P(\mathcal{R}, c - w(a))$, and is $\bot$ when no item of $G$ has weight at most $c$ (in
particular when $G$ is empty).

When addition in $\beta$ is monotone, $P$ is the best total value of a selection of total weight
at most $c$, and $\bot$ if there is none.
