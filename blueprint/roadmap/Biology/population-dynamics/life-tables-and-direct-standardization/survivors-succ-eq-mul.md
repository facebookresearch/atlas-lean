# Next-age survivors are survivors times one minus the death probability

Let $(l_x)$ and $(d_x)$ be real sequences indexed by the ages $x \in \mathbb{N}$ with
$l_{x+1} = l_x - d_x$ for every age $x$ (a closed cohort, whose survivors $l_x$ change only by the
deaths $d_x$). Then, at every age $x$ with $l_x > 0$, $l_{x+1} = l_x (1 - q_x)$, where
$q_x = d_x / l_x$ is the [death probability](death-probability.md). No sign condition on the deaths
is needed. When $0 \le d_x \le l_x$, the factor $1 - q_x$ lies in $[0, 1]$: it is the proportion of
the survivors at age $x$ who reach age $x + 1$, read as the probability of surviving from age $x$ to
age $x + 1$.

Source: Methods Protocol for the Human Mortality Database, version 6, eq. (78).
