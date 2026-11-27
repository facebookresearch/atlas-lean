# Expected penalized complete-data log-likelihood of GPS

For a finite set of events, real counts $N_j$, a real $\alpha$ and real weights $\pi_j$, put

$$Q_\alpha(\pi) = \sum_j (N_j - \alpha) \log \pi_j,$$

with the conventions $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$: the expected log-likelihood plus the log of the negative Dirichlet prior $\prod_j \pi_j^{-\alpha}$, up to a constant. It is meaningful for positive $\pi$.
