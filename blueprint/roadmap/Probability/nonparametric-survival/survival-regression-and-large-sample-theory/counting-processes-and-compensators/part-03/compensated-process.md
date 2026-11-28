# Compensated counting process

For a latent failure time $T$, censoring time $C$ and a measure $\Lambda$ on $\mathbb{R}$ (in the model, the hazard measure of the failure-time law), the compensated counting process is $M(t) = N(t) - A(t)$, where $N$ is the counting process and $A(t) = \int_{(-\infty, t]}Y\,d\Lambda$ is the compensator, with $Y$ the at-risk process; the integral is computed in $[0, \infty]$ and an infinite value is read as $A(t) = 0$, so then $M(t) = N(t)$.
