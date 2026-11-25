# Structural causal models and counterfactuals

A Markovian structural causal model assigns to every variable an autonomous mechanism
$X_k = f_k(X_{\mathrm{pa}(k)}, U_k)$ driven by mutually independent disturbances. Its law factorizes over its
causal diagram (the causal Markov condition), an intervention $\mathrm{do}(X = x)$ replaces the mechanisms
of the intervened variables by constants (the submodel $M_x$, whose law is the truncated
factorization of the [causal Bayesian network](../causal-bayesian-networks/README.md)), and a
counterfactual $Y_x(u)$ is the solution of that submodel for the unit $u$. These are the three
rungs of Pearl's hierarchy: association, intervention, counterfactual.

## Models and their law

- [Markovian structural causal model](scm.md)
- [Parent values in a structural causal model](pa-val.md)
- [Parent values in a structural causal model with node-wise noise](pa-val-2.md)
- [Solution of the structural equations](solve.md)
- [Solution of a structural causal model with node-wise noise](solve-2.md)
- [The solution satisfies the structural equations](solve-eq.md)
- [Uniqueness of the solution](solve-eq-iff.md)
- [Law of a structural causal model](law.md)
- [The disturbance law sums to one](sum-prod-noise.md)
- [Events under the law of a structural causal model](sum-law-filter.md)
- [Weights of an image law](std-simplex-map-weights.md)

## The causal Markov condition

- [The causal Bayesian network of a structural causal model](to-bayes-net.md)
- [The causal Markov condition](law-eq-joint.md)
- [The law of a structural causal model sums to one](sum-law.md)

## Interventions

- [The submodel of the intervention $\mathrm{do}(X_W = w)$](do-set.md)
- [Intervention on a set of nodes in a structural causal model with node-wise noise](do-set-2.md)
- [Disturbances of a submodel](do-set-noise.md)
- [Network of a submodel](joint-to-bayes-net-do-set.md)
- [Interventions are truncated factorizations](law-do-set.md)
- [Single-node interventions in a structural causal model](law-do-set-singleton.md)

## Counterfactuals

- [The unit-level counterfactual](counterfactual.md)
- [The single-node counterfactual in a structural causal model with node-wise noise](counterfactual-2.md)
- [Effectiveness](counterfactual-of-mem.md)
- [Effectiveness of the single-node counterfactual](counterfactual-self.md)
- [Consistency](counterfactual-eq-solve.md)
- [Consistency of the single-node counterfactual](counterfactual-eq-solve-2.md)
- [Counterfactual probability given evidence](cf-prob.md)
- [Without evidence, counterfactuals are interventions](cf-prob-true.md)
- [Evidence that agrees with the antecedent](cf-prob-of-consistent.md)
- [The probability of necessity under monotonicity](cf-prob-necessity.md)
- [Pearl's formula for the probability of necessity](cf-prob-necessity-eq.md)

## Related topics

- [Causal Bayesian networks](../causal-bayesian-networks/README.md): the truncated factorization,
  back-door and front-door adjustment and the do-calculus, which apply to the causal
  network of a model.
- [Bayesian networks](../bayesian-networks/README.md): the factorization and Markov properties
  that the causal Markov condition delivers.
- [Potential outcomes and causal identification](../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/README.md):
  the potential-outcome framework takes $Y_x(u)$ as primitive; here it is derived from the
  submodel $M_x$, and consistency becomes a theorem.
- [Additive noise models and causal identifiability](../additive-noise-models-and-causal-identifiability/README.md):
  restricting the structural equations to linear ones with additive non-Gaussian noise makes the
  causal direction identifiable from observational data, while the linear Gaussian case is not.

- [Response SCM](response-scm.md)

- [Finite recursive structural causal model](finite-scm.md)

- [Unique solvability of a recursive SCM](exists-unique-is-solution.md)

- [A Markovian SCM induces its Bayesian network](induced-law-eq-joint.md)
