# Survivors are the initial size times a product of survival factors

Let $(l_x)$ and $(d_x)$ be real sequences indexed by the ages $x \in \mathbb{N}$ with
$l_{k+1} = l_k - d_k$ for every age $k$ (a closed cohort), and let $x$ be an age with $l_k > 0$ for
every $k < x$. Then $l_x = l_0 \prod_{k < x} (1 - q_k)$, the product running over the ages
$k = 0, \dots, x - 1$, where $q_k = d_k / l_k$ is the [death probability](death-probability.md) at
age $k$. Only the survivors before age $x$ need be positive, so that each $q_k$ is defined; $l_x$
itself may be zero or negative. For $x = 0$ the product is empty, hence $1$, and the positivity
hypothesis is vacuous. When $0 \le d_k \le l_k$ for every $k < x$, each factor $1 - q_k$ lies in
$[0, 1]$ and is read as the probability of surviving from age $k$ to age $k + 1$.

Source: Methods Protocol for the Human Mortality Database, version 6, eq. (79).
