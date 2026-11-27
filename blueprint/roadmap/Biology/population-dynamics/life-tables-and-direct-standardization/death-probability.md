# Death probability as deaths over the number at risk

For real sequences $(l_x)$ and $(d_x)$ indexed by the ages $x \in \mathbb{N}$, and an age $x$ with
$l_x > 0$, the death probability at age $x$ is $q_x = d_x / l_x$. It is defined only when $l_x > 0$:
no division by zero occurs, and there is no value at an age with $l_x \le 0$, such as an age after a
cohort has died out.

In a life table, $l_x$ is the number alive at exact age $x$, the number at risk, and $d_x$ the
number of them who die before age $x + 1$, so that $0 \le d_x \le l_x$. Then $q_x$ lies in $[0, 1]$
([bounds](death-probability-mem-icc.md)): it is the proportion of those at risk who die in the age
interval $[x, x + 1)$, read as the probability of dying in that interval. For arbitrary real $d_x$
it is only a ratio, which can be negative or greater than $1$.

Source: Methods Protocol for the Human Mortality Database, version 6, eqs. (80) and (84).
