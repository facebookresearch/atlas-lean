# Time-changed Λ-coalescent limits of variable-size Cannings models

Let $(\tilde R^{(N)}_r)_{r \ge 0}$ be the ancestral partition of a sample of $n$ individuals in a modified Moran model with variable population sizes $(N_r)$ satisfying the size-profile condition with profile $\nu : [0, \infty) \to (0, \infty)$, and let $c_N$ be the pair-coalescence probability of the fixed-size model. Write $(x)_2 = x(x-1)$.

**Theorem 1.** Let $\Lambda$ be a probability measure on $[0, 1]$ for which $U'_N$ satisfies $\mathbb E[(U'_N)_2]/(N-1) \not\to 0$. Define the fixed-$N$ model by $U_N = U'_N \mathbf 1_{A_N} + 2(1 - \mathbf 1_{A_N})$ with events $A_N$ independent of $U'_N$ and

$$\frac{\mathbb E[(U'_N)_2]\,\mathbb P(A_N)}{(N)_2} = N^{-\gamma}, \qquad 1 < \gamma < 2.$$

Then there are population sizes with profile $\nu$ such that, in the Skorokhod sense,

$$\big(\tilde R^{(N)}_{\lfloor c_N^{-1} t \rfloor}\big)_{t \ge 0} \xrightarrow{d} \big(\Pi_{G(t)}\big)_{t \ge 0}, \qquad G(t) = \int_0^t \nu(s)^{-\gamma}\, ds,$$

where $(\Pi_t)$ is the $\Lambda$-$n$-coalescent; added individuals may be allocated in any way that keeps a modified Moran model.

**Corollary 1.** For $\Lambda = \mathrm{Beta}(a, b)$ with $a \in (0, 1)$, $b > 0$, a suitable modified Moran model with variable sizes satisfies the same convergence holds with $G(t) = \int_0^t \nu(s)^{a - 2}\, ds$ for every profile $\nu$.

**Theorem 3.** For the Cannings model obtained by sampling $N_{r-1}$ individuals from i.i.d. potential offspring with tail index $\alpha \in [1, 2)$ (Eq. 9), for every profile $\nu$ there are sizes with that profile such that the rescaled genealogy converges to $(\Pi_{G(t)})$ with $G(t) = \int_0^t \nu(s)^{1 - \alpha}\, ds$ and $(\Pi_t)$ the $\mathrm{Beta}(2 - \alpha, \alpha)$-$n$-coalescent.

## Depends on

- [Modified Moran model with variable population size](modified-moran-model-with-variable-population-size.md)
- [The Λ-coalescent rate matrix on partitions of a finite sample](../../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
- [Coalescence probability of a Cannings model](../../cannings-models/coal-prob.md)

## Proof depends on

- [Möhle–Sagitov conditions for a Λ-coalescent limit](../mohle-sagitov-lambda.md)

## Expansion

If the pair-coalescence probability scales as $c_N \sim C N^{-\gamma}$, a generation with size $N_r \approx \nu(t) N$ has coalescence probability $c_{N_r} \approx \nu(t)^{-\gamma} c_N$, so summing $c_{N_r}$ over $\lfloor c_N^{-1} t \rfloor$ generations gives $G(t)$ (Eq. 8). The proofs check a variable-size version of the Möhle–Sagitov conditions: the merger probabilities of generation $r$ equal those of a fixed-$N_r$ model up to errors whose sums over $O(c_N^{-1})$ generations vanish (Eq. 5). The Beta exponents follow from $c_N \propto N^{a - 2}$ for Beta$(a, b)$ with $a < 1$ and $c_N \propto N^{1 - \alpha}$ for Schweinsberg-type offspring laws.

## Sources

- F. Freund, *Cannings models, population size changes and multiple-merger coalescents*, J. Math. Biol. (2020). <https://doi.org/10.1007/s00285-020-01470-5> (PMCID: PMC7052052)
