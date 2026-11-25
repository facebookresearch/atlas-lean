# Single-node interventions in a structural causal model

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in a
nonempty set $\alpha$ and disturbances in a finite set. For a node $k$ and $a \in \alpha$, the law
of the submodel of $\mathrm{do}(X_k = a)$ is the joint distribution of the
[intervention](../causal-bayesian-networks/intervene.md) $\mathrm{do}(X_k = a)$ in the
[causal network](to-bayes-net.md) of $M$. Under their graphical and positivity conditions, the back-door
and front-door adjustments then compute it from the observational law; without them the intervention
need not be identified by that law.
