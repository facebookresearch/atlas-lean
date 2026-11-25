# Wright–Fisher limit of the no-coalescence probability

For every real $t \ge 0$,

$$\Bigl(1 - \frac{1}{M}\Bigr)^{\lfloor tM \rfloor} \to q_{22}(t) = e^{-t}$$

as the natural number $M$ tends to infinity, where $1 - 1/M$ is the [probability of no coalescence](../kingman-s-coalescent-and-watterson-s-estimator/no-coal-prob.md) of two lineages in one generation of a Wright–Fisher population of $M$ gene copies (with $1/0 = 0$) and $q_{22}$ is [Tavaré's probability](../ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md). In the three-species model, the lineages of species $0$ and $1$ have distinct parents in each of the $\lfloor tM \rfloor$ generations of the internal branch ($t$ coalescent units) with probability $(1 - 1/M)^{\lfloor tM \rfloor}$, and the limit is the weight of the case in which three lineages reach the root population.
