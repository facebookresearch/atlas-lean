# Consistency

**Consistency** (Pearl, *Statistics Surveys* 2009, eq. (36), $X = x \Rightarrow Y_x = Y$, which
§4.1 notes holds automatically under the structural definition): let $M$ be a Markovian
structural causal model on the nodes $0, \dots, n - 1$ with values in $\alpha$, let $W$ be a finite
set of nodes, $w \in \alpha^n$ and $u$ a disturbance value. If the solution $X(u)$ already
agrees with $w$ on $W$, forcing $X_W = w$ changes nothing: $X_{W \leftarrow w}(u) = X(u)$.

## Background

- [Observed outcome from potential outcomes](../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/observed.md):
  the same consistency rule, built into the potential-outcome framework.
