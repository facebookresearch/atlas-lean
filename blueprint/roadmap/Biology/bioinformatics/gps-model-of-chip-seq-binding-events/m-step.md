# The GPS M-step with component elimination

For a finite set of events, real counts $N_j$ and a real $\alpha$, the M-step update is

$$\hat\pi_j = \frac{\max(N_j - \alpha, 0)}{\sum_k \max(N_k - \alpha, 0)},$$

with the convention $x/0 = 0$ (so the update is the zero vector when no event survives).
