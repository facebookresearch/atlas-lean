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

## Finite structural causal models with node-wise noise

- [Response Law](response-law.md)
- [Every finite Bayesian network is induced by a Markovian SCM](response-scm-induced-law.md)
- [Response Weight](response-weight.md)
- [Response Weight nonneg](response-weight-nonneg.md)
- [Sum response Weight](sum-response-weight.md)
- [Is Solution](is-solution.md)
- [Eq solve](eq-solve.md)
- [Consistency of the potential outcomes](ae-eq-observed.md)
- [The back-door criterion implies conditional ignorability](cond-indep-discrete-of-backdoor.md)
- [Markovian ignorability](cond-indep-discrete-potential-outcomes.md)
- [Counterfactual Prob](counterfactual-prob.md)
- [Abduction, action, prediction](counterfactual-prob-eq-sum-posterior-wei.md)
- [Counterfactual Prob true](counterfactual-prob-true.md)
- [Surgery](do-node.md)
- [Do Node f of eq](do-node-f-of-eq.md)
- [Do Node f of ne](do-node-f-of-ne.md)
- [Do Node pa of ne](do-node-pa-of-ne.md)
- [Do Set f of mem](do-set-f-of-mem.md)
- [Do Set f of not mem](do-set-f-of-not-mem.md)
- [Do Set pa of not mem](do-set-pa-of-not-mem.md)
- [Evidence Prob](evidence-prob.md)
- [Induced Bayes Net](induced-bayes-net.md)
- [Induced Law](induced-law.md)
- [Surgery commutes with the do-operator](induced-law-do-node.md)
- [Induced Law do Set](induced-law-do-set.md)
- [Is Solution prefix](is-solution-prefix.md)
- [Map weights eq](map-weights-eq.md)
- [The potential-outcome law is the back-door formula](measure-real-counterfactual-eq-backdoor.md)
- [Noise Measure](noise-measure.md)
- [Noise Measure apply eq](noise-measure-apply-eq.md)
- [Noise Measure real eq](noise-measure-real-eq.md)
- [Noise Weight](noise-weight.md)
- [Noise Weight nonneg](noise-weight-nonneg.md)
- [Abduction](posterior-weight.md)
- [Potential Outcome](potential-outcome.md)
- [Real coord eq](real-coord-eq.md)
- [Solve Prefix](solve-prefix.md)
- [Solve Prefix ancestral](solve-prefix-ancestral.md)
- [Solve Prefix cast Succ](solve-prefix-cast-succ.md)
- [Solve Prefix eq solve](solve-prefix-eq-solve.md)
- [Solve Prefix last](solve-prefix-last.md)
- [Solve congr of ancestral](solve-congr-of-ancestral.md)
- [Composition](solve-do-node-do-node-of-counterfactual.md)
- [Solve do Node of ancestral](solve-do-node-of-ancestral.md)
- [Solve is Solution](solve-is-solution.md)
- [A parentless nondegenerate treatment is ignorable](strongly-ignorable-of-pa-eq-empty.md)
- [Strong ignorability given the parents](strongly-ignorable-potential-outcomes.md)
- [Sum noise Weight eq one](sum-noise-weight-eq-one.md)
- [Sum posterior Weight](sum-posterior-weight.md)
- [Treated](treated.md)

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
