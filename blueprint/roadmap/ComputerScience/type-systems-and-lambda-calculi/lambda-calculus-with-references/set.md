# Assignment preserves store typing

Let the store $\mu$ be well typed under the variable
context $\Gamma$ and the store typing $S$, and let $l$ be a location to which $S$ assigns the
type $T$. If $v$ is a value of type $T$ under $\Gamma$ and $S$, then the store obtained from
$\mu$ by overwriting the entry at $l$ with $v$ is well typed under $\Gamma$ and $S$.

This is TAPL Lemma 13.5.5.
