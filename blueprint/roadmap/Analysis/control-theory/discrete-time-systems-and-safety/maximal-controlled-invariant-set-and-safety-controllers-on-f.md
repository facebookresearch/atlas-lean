# Maximal controlled invariant set and safety controllers on finite systems

This node collects the safety-controller synthesis results for finite nondeterministic control systems
and their reading as finite safety games.

## Expansion

A sound expansion has separate pages for:

1. **Model and controllable predecessor.** A finite system is $(X, U, \mathrm{Post})$ with
   $\mathrm{Post} : X \times U \to 2^X$. An input $u$ is enabled at $x$ when
   $\mathrm{Post}(x,u) \ne \emptyset$, so that a controller never chooses a blocking input. A state with no
   enabled input is a deadlock. Deadlocks are treated as losing for the controller: a play that reaches a
   deadlock is finite, and safety for $S$ requires every play to be infinite and to stay in $S$. (Under the
   alternative hypothesis that every state has an enabled input, there are no deadlocks and the two readings
   agree.) For $Y \subseteq X$, $\mathrm{CPre}(Y) = \{x : \exists u \text{ enabled at } x,\ \mathrm{Post}(x,u)
   \subseteq Y\}$; deadlocks are never in $\mathrm{CPre}(Y)$.
2. **Maximal controlled invariant subset.** For a safe set $S$, the greatest fixed point $W$ of
   $Y \mapsto S \cap \mathrm{CPre}(Y)$ is reached by the decreasing iteration $Y_0 = S$,
   $Y_{i+1} = S \cap \mathrm{CPre}(Y_i)$ after at most $\lvert S \rvert$ strict decreases. For example, if
   $S = \{x\}$ and $x$ is a deadlock, then $W = \emptyset$.
3. **Safety controller.** A memoryless controller that chooses, at each $x \in W$, an enabled $u$ with
   $\mathrm{Post}(x,u) \subseteq W$ makes every play from an initial state in $W$ infinite and keeps it inside $S$;
   from any initial state outside $W$, no controller, with or without memory, does so.
4. **Game reading.** Add an absorbing sink state $\bot$, reached from every deadlock, so that every position of
   the resulting turn-based game has a successor: the controller picks an enabled input, the environment picks a
   successor in $\mathrm{Post}(x,u)$, and deadlocks move to $\bot$. Then $W$ is the controller's winning region for
   the safety objective $S$, and its complement (with $\bot$) is the environment's attractor of
   $(X \setminus S) \cup \{\bot\}$; both players have memoryless winning strategies. The reachability and safety
   duality of the cited source is stated for game graphs in which every state has a successor, which the sink
   provides.

## Depends on

- [Attractor](../../../TheoryOfComputation/omega-automata-and-games/parity-games/attractor.md)

## Sources

- B. Jobstmann, *Reachability and Büchi games*, lecture slides, Bucharest, May 2010: reachability games
  via attractors with memoryless winning strategies, game graphs in which every state has a successor,
  and safety games as the dual of reachability games. <http://www-verimag.imag.fr/~iosif/LAT/w2_wed_3.pdf>
