# Store-typing weakening

Let $\Gamma$ be a variable context and let $S$ and $S'$ be store
typings such that $S$ is a prefix of $S'$. If a term $t$ has type $T$ under $\Gamma$ and $S$,
then $t$ has type $T$ under $\Gamma$ and $S'$.

This is TAPL Lemma 13.5.6, with the extension of store typings taken as the prefix order on
lists.
