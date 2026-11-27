# Hajek's theorem for the logarithmic cooling schedule

Let $S$ be a finite state space, $R : S \to \mathrm{PMF}(S)$ a proposal kernel and $V : S \to \mathbb{R}$ an energy. Assume the landscape $(R, V)$ is strongly irreducible (every state reaches every other along proposal arcs staying below some height) and weakly reversible (for every height $E$, $i$ is reachable from $j$ at height $E$ if and only if $j$ is reachable from $i$ at height $E$). Let $c > 0$, $x_0 \in S$, and run simulated annealing from $x_0$ with Metropolis acceptance $\min\bigl(1, e^{-\max(V(y) - V(x), 0)/T}\bigr)$, where step $k \to k+1$ uses temperature

$$T_{k+1} = \frac{c}{\log(k + 2)}.$$

Let $S^* = \{s : V(s) \le V(t) \text{ for all } t\}$ be the set of global minima, and let $d^*$ be the largest escape depth of a local minimum that is not a global minimum ($0$ if there is none). Then the annealing chain $X_k$ converges in probability to $S^*$,

$$\lim_{k \to \infty} \Pr(X_k \in S^*) = 1,$$

if and only if $d^* \le c$. Here $d^*$ is read as a real number, with an infinite value counted as $0$.

## Related topics

- [Hajek's cooling-schedule theorem](hajek-s-cooling-schedule-theorem.md): the general criterion $\sum_k e^{-d^*/T_k} = \infty$ for any cooling schedule, of which this is the logarithmic case.

## Sources

- Bruce Hajek, "Optimization by simulated annealing: a necessary and sufficient condition for convergence", Adaptive Statistical Procedures and Related Topics, IMS Lecture Notes–Monograph Series, vol. 8 (1986), pp. 417–427, doi:10.1214/lnms/1215540316.
