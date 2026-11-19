# One-step transition probabilities of the Moran process

For a real number $r$ and a natural number $N$, the transition weights on the mutant counts $\{0, \dots, N\}$: from state $i$ to state $j$,

- the [up-step probability](moran-up.md) $a_i$ if $j = i + 1$;
- the [down-step probability](moran-down.md) $b_i$ if $j = i - 1$;
- $1 - a_i - b_i$ if $j = i$;
- $0$ otherwise.

For $r > 0$ they are the one-step transition probabilities of the Moran process with $N$ individuals and mutant relative fitness $r$.
