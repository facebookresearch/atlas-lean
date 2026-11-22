# Greenwood's variance estimate

Greenwood's estimate of the variance of the Kaplan–Meier estimate at $t$ is

$$\hat V(t) = \hat S(t)^2 \sum_{t_j \le t, \ d_j < Y_j} \frac{d_j}{Y_j (Y_j - d_j)}.$$

This is Greenwood's plug-in estimate of the variance of $\hat S(t)$, not the exact sampling variance of
the Kaplan–Meier estimator. The textbook summand is undefined when $d_j = Y_j$ (if also $d_j > 0$, the
Kaplan–Meier factor $1 - d_j / Y_j$ is $0$), so such times are left out of the sum. If no such time occurs
by $t$, the definition is the textbook formula; if one occurs with $d_j > 0$ at or before $t$, then
$\hat S(t) = 0$ and $\hat V(t) = 0$.
