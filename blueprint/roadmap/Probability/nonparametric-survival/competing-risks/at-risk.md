# Number at risk in competing-risks data

Consider right-censored competing-risks data grouped at the observation times
$t_1 < \dots < t_k$, with $d_{j,c}$ subjects failing from cause $c$ and $c_j$ subjects censored at
$t_j$. The number at risk at $t_j$ is $n_j = \sum_{l \ge j} \bigl(\sum_c d_{l,c} + c_l\bigr)$, the
number of subjects whose observation time is at least $t_j$. It is the
[number at risk](../kaplan-meier-estimator/at-risk.md) of the same data with the failures from all
causes pooled.
