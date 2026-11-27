# Completion time on a single machine

Let $\sigma$ be a list of jobs and let $p_j$ be the
processing time of job $j$, in an additive monoid such as $\mathbb{N}$ or $\mathbb{R}$. When the
machine processes the jobs of $\sigma$ one after another from time $0$, without idle time or
preemption, job $j$ completes at time $C_j$, the sum of $p_i$ over the entries $i$ of $\sigma$ up
to and including the first occurrence of $j$. If $j$ does not occur in $\sigma$, $C_j$ is the sum
of $p_i$ over all of $\sigma$.
