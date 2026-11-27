# Interventions are truncated factorizations

**Interventions are truncated factorizations** (Pearl, *Statistics Surveys* 2009,
Corollary 1, eq. (17); Pearl 1995, eq. (5)): let $M$ be a Markovian structural causal model on
the nodes $0, \dots, n - 1$ with values in a nonempty set $\alpha$ and disturbances in a finite
set, $W$ a finite set of nodes and $w \in \alpha^n$. The law of the submodel of
$\mathrm{do}(X_W = w)$ is the joint distribution of the [causal network](to-bayes-net.md) of $M$
with the arrows into $W$ removed and point masses at $w_j$ for $j \in W$.

Pearl derives the truncated factorization by noting that the submodel of an intervention is
again a Markovian model, so the causal Markov condition applies to it.
