# Covering recurrence for multiple-choice knapsack

Let $\beta$ be a linearly ordered additive commutative monoid, and let $\beta_\bot$ be $\beta$
with a new least element $\bot$ adjoined, with $\bot + x = x + \bot = \bot$. For a list of groups of
knapsack items with values in $\beta$ and a target $L \in \mathbb{N}$, the covering recurrence $C$
takes values in $\beta_\bot$ and is defined by recursion on the groups. With no groups,
$C(L) = 0$ if $L = 0$ and $C(L) = \bot$ otherwise. For a first group $G$ followed by the remaining
groups $\mathcal{R}$, $C(G\mathcal{R}, L)$ is the maximum, over the items $a \in G$, of
$v(a) + C(\mathcal{R}, L \mathbin{\dot-} w(a))$, where $\dot-$ is subtraction truncated at $0$, and
is $\bot$ when $G$ is empty.

When addition in $\beta$ is monotone, $C$ is the best total value of a selection of total weight
at least $L$, and $\bot$ if there is none.
