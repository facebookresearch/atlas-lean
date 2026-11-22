# The update is an upper bound for the truncated objective

Suppose $\alpha < N_{j_0}$ for some event $j_0$. Then for every $\pi$ with $\pi_j > 0$ for all $j$ and $\sum_j \pi_j = 1$,

$$\tilde Q_\alpha(\pi) \le \tilde Q_\alpha(\hat\pi),$$

where $\tilde Q_\alpha$ is the [truncated objective](truncated-q.md) and $\hat\pi$ the [M-step update](m-step.md). Here $\hat\pi$ lies on the closed probability simplex, with $\hat\pi_j = 0$ exactly for the eliminated events $N_j \le \alpha$; when some event is eliminated it is not itself a positive vector.
