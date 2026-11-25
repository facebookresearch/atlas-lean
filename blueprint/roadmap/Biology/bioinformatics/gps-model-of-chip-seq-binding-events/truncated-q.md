# Truncated GPS objective

For a finite set of events, real counts $N_j$, a real $\alpha$ and real weights $\pi_j$, put

$$\tilde Q_\alpha(\pi) = \sum_j \max(N_j - \alpha, 0) \log \pi_j,$$

with the conventions $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$.
