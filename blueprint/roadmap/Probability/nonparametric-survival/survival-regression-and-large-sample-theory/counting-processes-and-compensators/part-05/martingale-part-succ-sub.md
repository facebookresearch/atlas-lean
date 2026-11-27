# Increment of the compensated process

For a process $N$ on a filtered measure space $(\Omega, \mathcal F, \mu)$ with an arbitrary measure $\mu$, the martingale part $M$ of its Doob decomposition has increments $M_{n+1} - M_n = (N_{n+1} - N_n) - \mu[N_{n+1} - N_n \mid \mathcal F_n]$, where $\mu[\cdot \mid \mathcal F_n]$ is Mathlib's conditional expectation (the zero function when $\mu$ is not σ-finite on $\mathcal F_n$ or the increment is not integrable).
