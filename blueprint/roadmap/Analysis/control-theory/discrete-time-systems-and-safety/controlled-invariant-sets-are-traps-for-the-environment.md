# Controlled invariant sets are traps for the environment

Let $(X, U, \mathrm{Post})$ be a finite system, $S \subseteq X$ a safe set and $W$ its maximal controlled invariant subset, and consider the turn-based game of the
controlled-invariance page: controller positions $x \in X$ and the sink $\bot$, and environment positions $(x, u)$ with $u$ enabled at $x$. The set
$W' = W \cup \{(x, u) : x \in W,\ u \text{ enabled at } x,\ \mathrm{Post}(x, u) \subseteq W\}$ is a trap for the environment: from every environment position in $W'$ every
move stays in $W'$, and from every controller position in $W'$ some move stays in $W'$. Every position of $W'$ other than the environment positions lies in $S$.

## Proof

From $(x, u) \in W'$ the environment moves to some $y \in \mathrm{Post}(x, u) \subseteq W \subseteq W'$. A controller position $x \in W$ is in $\mathrm{CPre}(W)$, because $W$ is a fixed
point of $Y \mapsto S \cap \mathrm{CPre}(Y)$; so some enabled $u$ has $\mathrm{Post}(x, u) \subseteq W$, and the move to $(x, u)$ stays in $W'$. Deadlocks are never in $\mathrm{CPre}$, so
no position of $W$ moves to $\bot$, and $W \subseteq S$.

## Depends on

- [Maximal controlled invariant set and safety controllers on finite systems](maximal-controlled-invariant-set-and-safety-controllers-on-f.md)
- [Trap for a player](../../../TheoryOfComputation/omega-automata-and-games/parity-games/is-trap.md)

## Sources

- B. Jobstmann, *Reachability and Büchi games*, lecture slides, Bucharest, May 2010 (safety games as duals of reachability games; traps). Background reference. <http://www-verimag.imag.fr/~iosif/LAT/w2_wed_3.pdf>
