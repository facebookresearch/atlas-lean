# Bottom-up packing table for multiple-choice knapsack

Let $\beta$ be a linearly ordered additive commutative monoid and $\beta_\bot$ the extension of
$\beta$ by a least element $\bot$ absorbing for addition. For a maximal capacity $K \in \mathbb{N}$,
the bottom-up packing table of a list of groups of knapsack items is a list of $K + 1$ entries
in $\beta_\bot$, defined by recursion on the groups. With no groups it consists of $K + 1$ zeros.
For a first group $G$ followed by the remaining groups, let $N$ be the table of the remaining
groups; the entry at capacity $c \in \{0, \dots, K\}$ is the maximum, over the items $a \in G$
with weight $w(a) \le c$, of $v(a) + N[c - w(a)]$, and is $\bot$ when no item of $G$ has weight at
most $c$. Each row is thus computed from the next by one scan of its group per capacity.
