# Hajek's cooling-schedule theorem

Let $V$ be a real function on a finite nonempty set $S$, let each state $s$ have a set $N(s) \subseteq S$ of neighbours, and let
$R$ be a transition matrix on $S$ with $R(s, s') > 0$ exactly when $s' \in N(s)$. A state $s'$ is reachable from $s$ at height $E$ if there is a
path $s = s_0, s_1, \dots, s_p = s'$ with $R(s_i, s_{i+1}) > 0$ and $V(s_i) \le E$ for $0 \le i \le p$. Assume strong
irreducibility (every state is reachable from every other at some height) and weak reversibility (for every real $E$,
$s'$ is reachable from $s$ at height $E$ if and only if $s$ is reachable from $s'$ at height $E$). A state $s$ is a local
minimum if no state $s'$ with $V(s') < V(s)$ is reachable from $s$ at height $V(s)$; the depth of a local minimum that is
not a global minimum is the least $E > 0$ such that some $s'$ with $V(s') < V(s)$ is reachable from $s$ at height $V(s) + E$. Simulated annealing with temperatures
$T_1 \ge T_2 \ge \dots > 0$, $T_k \to 0$, proposes $Y$ from $N(X_k)$ according to $R(X_k, \cdot)$ and sets $X_{k+1} = Y$ with
probability $\exp(-\max(V(Y) - V(X_k), 0)/T_{k+1})$ and $X_{k+1} = X_k$ otherwise. Let $d^*$ be the largest depth of a local minimum
that is not a global minimum, and $d^* = 0$ if every local minimum is global. (The source uses $T_k$ for the step from
$X_k$; the shift to $T_{k+1}$ changes neither condition below.) Then
$\lim_{k \to \infty} \Pr[X_k \text{ is a global minimum}] = 1$ for every initial state if and only if
$\sum_k \exp(-d^*/T_k) = \infty$. In particular, for $T_k = c/\log(k+1)$ with $c > 0$, this holds if and only if $c \ge d^*$;
the equality case is included, since the series is then $\sum_k (k+1)^{-1}$.

## Expansion

This node states a precise result; the cup and escape-time estimates of the source are its proof. A good expansion adds a
page for the pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: the exit-time estimates for cups on which the source's proof rests.

## Related topics

- [Fixed-temperature Gibbs law and zero-temperature concentration](fixed-temperature-gibbs-law-and-zero-temperature.md)

## Sources

- B. Hajek, *Optimization by simulated annealing: a necessary and sufficient condition for convergence*, in *Adaptive
  Statistical Procedures and Related Topics*, IMS Lecture Notes 8 (1986), 417–427: the model and hypotheses SI and WR
  (pp. 418–419), the definitions of height reachability, local minima and depth (p. 419), cups (p. 421), Theorem 1 (pp.
  422–423: non-local-minima carry vanishing mass, and the bottom of a cup of depth $d$ formed by local minima of depth $d$
  carries vanishing mass if and only if $\sum_k \exp(-d/T_k) = \infty$; the displayed condition (4) prints $d^*$ for $d$),
  the remark that for $T_k = c/\log(k+1)$ the condition holds if and only if $c \ge d^*$ (p. 423), and the abstract (p. 417)
  for convergence in probability to the global minima. <https://courses.physics.illinois.edu/ece544na/fa2014/hajek_annealing.pdf>
