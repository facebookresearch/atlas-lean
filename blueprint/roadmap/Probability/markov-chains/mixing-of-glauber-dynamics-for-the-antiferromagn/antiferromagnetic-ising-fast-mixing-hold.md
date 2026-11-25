# O(n log n) mixing of antiferromagnetic Glauber dynamics in the uniqueness regime

For a graph $G$ on $n$ vertices and $\beta > 0$, the zero-field antiferromagnetic Ising model gives a spin configuration $\sigma \in \{\pm1\}^n$ weight proportional to $\exp(-\beta\sum_{uv \in E}\sigma_u\sigma_v)$, and its Glauber (heat-bath) dynamics resamples the spin of a uniformly random vertex from its conditional law given the others. For $d \ge 3$ and $\beta > 0$ with $(d - 1)\tanh\beta < 1$, the Glauber dynamics on $d$-regular $n$-vertex graphs mixes in $O(n\log n)$ steps, uniformly over the graphs. This follows from the optimal mixing theorem of Chen, Liu and Vigoda (2021) in the tree-uniqueness regime.

## Sources

- Problem: AimPL: Markov chain mixing times, Problem 1.3, http://aimpl.org/markovmixing/1/.
- Resolution: Z. Chen, K. Liu and E. Vigoda, Optimal mixing of Glauber dynamics: entropy factorization via high-dimensional expansion, Proceedings of the 53rd Annual ACM SIGACT Symposium on Theory of Computing (STOC 2021), 1537-1550, arXiv:2011.02075, https://doi.org/10.1145/3406325.3451035.
