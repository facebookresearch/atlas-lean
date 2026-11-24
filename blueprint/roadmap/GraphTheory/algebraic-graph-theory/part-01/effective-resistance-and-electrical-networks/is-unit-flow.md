# Unit flow

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with oriented incidence matrix $B$, $B_{x e} = [x = e^-] - [x = e^+]$. For $s, t \in V$, an edge function $\theta : E \to \mathbb{R}$ is a unit flow from $s$ to $t$ if

$$B \theta = \delta_s - \delta_t, \qquad (B\theta)(x) = \sum_{e:\ e^- = x} \theta_e - \sum_{e:\ e^+ = x} \theta_e.$$

For $s \ne t$ this says that the net outflow is $1$ at $s$, $-1$ at $t$ and $0$ at every other vertex (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.4: a flow from $A$ to $Z$ of strength $1$, with $A = \{s\}$ and $Z = \{t\}$). For $s = t$ the right side is $0$, so a unit flow from $s$ to $s$ is a circulation, with net outflow $0$ at every vertex.

## Background

- [Feasible flow](../../../matchings-and-flows/max-flow-min-cut-theorem/is-feasible-flow.md): flows subject to capacities, the setting of the max-flow min-cut theorem; unit flows here have no capacities and are compared by energy instead.
