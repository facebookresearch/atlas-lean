# Well-typed stores

Let $\Gamma$ be a variable context and $S$ a store typing. A store
$\mu$, a list of terms whose entry at index $l$ is the contents of location $l$, is well typed
under $\Gamma$ and $S$, written $\Gamma \mid S \vdash \mu$, when $\mu$ and $S$ have the same
length and, for every location $l$ less than this length, the entry of $\mu$ at $l$ is a value
that has, under $\Gamma$ and $S$, the type that $S$ assigns to $l$.

Stores here are lists of terms rather than of values, so each entry is required to be a value.

## Sources

- TAPL Definition 13.5.1.
