# Planner answer

A path problem on a topological space $C$ consists of a free set $F \subseteq C$, a start $q_I \in F$ and a goal $q_G \in F$.

For a path problem $P$ with start $q_I$ and goal $q_G$, a planner answer for $P$ is one of three things:

- $\mathrm{found}(\gamma)$, carrying a continuous path $\gamma : [0,1] \to C$ from $q_I$ to $q_G$;
- $\mathrm{noPath}$, a report that no path exists;
- $\mathrm{running}$, meaning no answer yet.

The path carried by $\mathrm{found}$ is not required to stay in the free set.
