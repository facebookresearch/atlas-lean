# Reachability probabilities and logical reduction of Boolean networks

**Random walk on the asynchronous transition graph.** Let $\mathcal A$ be the [asynchronous transition graph](asynchronous-transition-graph-and-stable-states-of-a-boolean-network.md) of a Boolean network $F$ on $\{0,1\}^n$, and give every arc leaving a state $x$ the same probability $1/|\mathrm{succ}(x)|$. This defines a Markov chain on $\{0,1\}^n$ whose absorbing states are the stable states. Suppose every terminal strongly connected component is a stable state. For a set $\Phi$ of stable states forming a phenotype (for example all survival states), the probability that the walk started in the set $X_0$ of initial conditions (uniformly) is absorbed in $\Phi$ is

$$\pi(\Phi) = \frac{1}{|X_0|}\sum_{x \in X_0} h_\Phi(x), \qquad h_\Phi(x) = \begin{cases} 1 & x \in \Phi,\\ 0 & x \text{ stable},\ x \notin \Phi,\\ \dfrac{1}{|\mathrm{succ}(x)|}\displaystyle\sum_{y \in \mathrm{succ}(x)} h_\Phi(y) & \text{otherwise},\end{cases}$$

and $h_\Phi$ is the unique solution of this linear system. Summed over a partition of the stable states into phenotypes, the $\pi$'s add up to $1$. Mutants (variables fixed to $0$ or $1$) and treatments are modelled by modifying $F$ and recomputing $\pi$, so phenotype probabilities can be compared across model variants even though the uniform arc weights are not calibrated rates.

**Logical reduction.** Let variable $v$ have rule $f_v$ not depending on $x_v$. Hiding $v$ replaces $x_v$ by $f_v(x)$ in the rules of all its targets and removes $v$. Then the stable states of the reduced network are exactly the projections of the stable states of the original network (no stable state is created or lost), and each regulatory influence that passed through $v$ is retained as a direct (possibly combined) influence. Example: with $\mathrm{BCL2} = \mathrm{NF\kappa B}$, $\mathrm{BAX} = \mathrm{C8} \wedge \neg\mathrm{BCL2}$, $\mathrm{MPT} = \mathrm{ROS} \wedge \neg\mathrm{BCL2}$ and $\mathrm{MOMP} = \mathrm{MPT} \vee \mathrm{BAX}$, removing BCL2 and then BAX gives

$$\mathrm{MPT}' = \mathrm{ROS} \wedge \neg\mathrm{NF\kappa B}, \qquad \mathrm{MOMP}' = \mathrm{MPT} \vee (\mathrm{C8} \wedge \neg\mathrm{NF\kappa B}).$$

## Depends on

- [Asynchronous transition graph and stable states of a Boolean network](asynchronous-transition-graph-and-stable-states-of-a-boolean-network.md)

## Expansion

The absorption probabilities $h_\Phi$ satisfy first-step analysis: from a non-stable state the walk moves to each successor with equal probability. Because every terminal component is a stable state, from every state some stable state is reachable, so the walk is absorbed with probability one and the system has a unique bounded solution (the transient part of the transition matrix has spectral radius below $1$). The equivalent path-counting description used in the source weights each path from an initial condition to a phenotype by the product of the branching probabilities along it. For the reduction: at a stable state of the original network $x_v = f_v(x)$, so substituting $f_v$ for $x_v$ leaves every target rule's value unchanged, and the projected state is stable in the reduced network; conversely a stable state of the reduced network extends uniquely to the original by setting $x_v = f_v(x)$, which is consistent because $f_v$ does not depend on $x_v$. Transient dynamics and cyclic attractors are not in general preserved by reduction, which is why the source compared simulations of the master and reduced models.

## Sources

- L. Calzone, L. Tournier, S. Fourquet, D. Thieffry, B. Zhivotovsky, E. Barillot, A. Zinovyev, "Mathematical modelling of cell-fate decision in response to death receptor engagement", PLoS Computational Biology (2010), Methods ("Boolean formalism, synchronous vs. asynchronous strategy": equal arc probabilities; "Model reduction": BCL2/BAX example) and Results ("Reachability of phenotypes"), <https://doi.org/10.1371/journal.pcbi.1000702> (PMC2832675).
