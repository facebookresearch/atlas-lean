# Completeness of forward and backward simulations

If $A \le_{\ast T} B$, then there is an automaton $C$ with a [forward simulation](forward-simulations-are-sound.md) from $A$ to $C$ and a [backward simulation](backward-simulations-are-sound.md) from $C$ to $B$; if moreover $B$ has finite invisible nondeterminism, the backward simulation can be chosen image-finite. One may take for $C$ the canonical automaton of the finite traces of $A$, whose states are the finite traces of $A$ and whose steps extend a trace by one action; it is a deterministic forest with the same finite traces as $A$.

## Depends on

- [Forward simulations are sound for trace inclusion](forward-simulations-are-sound.md)
- [Backward simulations are sound for trace inclusion](backward-simulations-are-sound.md)

## Proof depends on

- [Forward simulations are complete for deterministic targets](forward-simulations-are-complete-for-deterministic-targets.md)
- [Backward simulations are complete for forest sources](backward-simulations-are-complete-for-forest-sources.md)

## Sources

- N. Lynch and F. Vaandrager, "Forward and backward simulations, Part I: Untimed systems", *Information and Computation* 121(2):214–233, 1995; author version of the journal paper, October 31, 1994, <https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf>, Section 2.3 (canonical automata, Lemma 2.9) and Section 3.4, Theorem 3.22.
