# Pivot termination from a potential

Let $\mathrm{step} : S \to S$ and $\Phi : S \to \mathbb{N}$ with $\Phi(s) \le B$ for all $s$, and suppose every non-fixed step strictly increases the potential: $\mathrm{step}(s) \ne s$ implies $\Phi(s) < \Phi(\mathrm{step}(s))$. Then from any start $s$, the iterates reach a fixed point within $B + 1$ steps: $\mathrm{step}^{k+1}(s) = \mathrm{step}^k(s)$ for some $k \le B + 1$. Bland's anti-cycling rule supplies such a potential through its lexicographic objective.
