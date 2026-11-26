# Optimality of the Euclidean integral filling coefficient

Write $\omega_{n+1}$ for the Euclidean volume of the open unit ball in $\mathbb R^{n+1}$ and put $a_n=(n+1)\omega_{n+1}$ and $c_n=1/((n+1)a_n^{1/n})$. The source uses integral metric currents in the finite-mass sense, with integer rectifiability for both $T$ and $\partial T$: disjoint images of bounded Borel bi-Lipschitz coordinate pieces, integrable integer multiplicities, and summable masses. Mass is the infimum of the total masses of finite measures bounding the current on a bounded Lipschitz coefficient and unit-Lipschitz coordinate functions.

For every integer $n\ge2$, there is a compactly supported integral $n$-cycle $T$ of strictly positive mass in $\mathbb R^{n+1}$ such that every compactly supported integral $(n+1)$-current $S$ in that same space with $\partial S=T$ satisfies $\mathbf M(S)\ge c_n\mathbf M(T)^{(n+1)/n}$. No arbitrary ambient-space sharpness or extra equality classification is asserted.

## Depends on

- Metric currents and boundary with compact support, integer rectifiability, induced Euclidean volume.

## Proof depends on

- Current of the unit sphere and a calibration or equivalent lower bound for every filling.

## Expansion

Build the sphere cycle and unit-ball current in the same metric-current model, then evaluate their masses and prove the lower estimate for arbitrary fillings, including every allowed multiplicity.

## Sources

- OpenAI Math, [`coefficient_optimal`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FillingCoefficient.lean#L120-L127) (statement and local definitions).
