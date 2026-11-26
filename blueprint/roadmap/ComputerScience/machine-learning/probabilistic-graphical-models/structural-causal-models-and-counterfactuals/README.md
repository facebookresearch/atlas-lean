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

- [Law of a node's response function](response-law.md)
- [Every finite Bayesian network is induced by a Markovian SCM](response-scm-induced-law.md)
- [Weight of a response function](response-weight.md)
- [Response-function weights are nonnegative](response-weight-nonneg.md)
- [Response-function weights sum to one](sum-response-weight.md)
- [Solutions of structural equations](is-solution.md)
- [Every solution is the value of the solution map](eq-solve.md)
- [Consistency of the potential outcomes](ae-eq-observed.md)
- [The back-door criterion implies conditional ignorability](cond-indep-discrete-of-backdoor.md)
- [Markovian ignorability](cond-indep-discrete-potential-outcomes.md)
- [Conditional counterfactual probability](counterfactual-prob.md)
- [Abduction, action, prediction](counterfactual-prob-eq-sum-posterior-wei.md)
- [Counterfactual probability under trivial evidence](counterfactual-prob-true.md)
- [Surgery](do-node.md)
- [The structural map at the intervened node is constant](do-node-f-of-eq.md)
- [The structural map away from the intervened node](do-node-f-of-ne.md)
- [Parents away from the intervened node](do-node-pa-of-ne.md)
- [The structural map on the intervened set is constant](do-set-f-of-mem.md)
- [The structural map away from the intervened set](do-set-f-of-not-mem.md)
- [Parents away from the intervened set](do-set-pa-of-not-mem.md)
- [Probability of factual evidence](evidence-prob.md)
- [Bayesian network induced by a structural causal model](induced-bayes-net.md)
- [Observational law of a structural causal model](induced-law.md)
- [Surgery commutes with the do-operator](induced-law-do-node.md)
- [Law of a structural causal model after surgery](induced-law-do-set.md)
- [Solutions agree with every prefix](is-solution-prefix.md)
- [Push-forward of the noise law is the induced law](map-weights-eq.md)
- [The potential-outcome law is the back-door formula](measure-real-counterfactual-eq-backdoor.md)
- [Product noise measure](noise-measure.md)
- [Product noise measure of a set](noise-measure-apply-eq.md)
- [Real value of the product noise measure of a set](noise-measure-real-eq.md)
- [Product weight of a noise value](noise-weight.md)
- [Product noise weights are nonnegative](noise-weight-nonneg.md)
- [Abduction](posterior-weight.md)
- [Potential outcome after an intervention](potential-outcome.md)
- [Product noise measure of a coordinate event](real-coord-eq.md)
- [Values of the first nodes](solve-prefix.md)
- [Prefixes on a parent-closed set depend only on its noise](solve-prefix-ancestral.md)
- [Extending a prefix keeps the earlier values](solve-prefix-cast-succ.md)
- [Every prefix restricts the solution map](solve-prefix-eq-solve.md)
- [The last value of a prefix follows its structural equation](solve-prefix-last.md)
- [On an ancestral set the solution depends only on its noise](solve-congr-of-ancestral.md)
- [Composition](solve-do-node-do-node-of-counterfactual.md)
- [Surgery outside an ancestral set leaves its solution unchanged](solve-do-node-of-ancestral.md)
- [The solution map solves the structural equations](solve-is-solution.md)
- [A parentless nondegenerate treatment is ignorable](strongly-ignorable-of-pa-eq-empty.md)
- [Strong ignorability given the parents](strongly-ignorable-potential-outcomes.md)
- [Product noise weights sum to one](sum-noise-weight-eq-one.md)
- [Posterior noise weights sum to one](sum-posterior-weight.md)
- [Treated event](treated.md)

## Cross-world counterfactuals in a binary model

- [Binary structural causal model with shared noise](binary-scm.md)
- [Interventions on a binary structural causal model](intervention.md)
- [Noise law of a binary structural causal model](is-noise-law.md)
- [Interventional law of a binary structural causal model](law-2.md)
- [Value of the cause under an intervention](sol-x.md)
- [Value of the effect under an intervention](sol-y.md)
- [Probability of the cross-world event Y₁ = 1, Y₀ = 0](prob-y1-y0.md)
- [Constant-response causal model](constant-response.md)
- [Switching-response causal model](switching-response.md)
- [The constant- and switching-response noise weights are probability laws](is-noise-law-constant-response-switching.md)
- [The constant- and switching-response models have the same interventional laws](law-constant-response-eq-switching-respo.md)
- [The constant-response model gives the cross-world event probability 0](prob-y1-y0-constant-response.md)
- [The switching-response model gives the cross-world event probability 1/2](prob-y1-y0-switching-response.md)
- [Cross-world counterfactuals are not identified by interventional laws](exists-same-law-ne-prob-y1-y0.md)

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
