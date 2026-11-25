# Chinese restaurant process

For a real number $\theta > 0$, the Chinese restaurant process with parameter $\theta$ is the sequence of probability distributions $\mathrm{CRP}_n$ on the set partitions of $\{0, \dots, n-1\}$ defined recursively: $\mathrm{CRP}_0$ is the point mass at the partition with no blocks, and $\mathrm{CRP}_{n+1}$ draws a partition $\pi$ from $\mathrm{CRP}_n$ and then applies [one step of the process](crp-step.md) to $\pi$.

## Sources

- D. J. Aldous, *Exchangeability and related topics*, in École d'Été de Probabilités de Saint-Flour XIII — 1983, Lecture Notes in Math. 1117, Springer (1985), §11.
- J. Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Math. 1875, Springer (2006), ch. 3.
