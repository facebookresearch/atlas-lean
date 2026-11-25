# Allocation preserves store typing

Let $\Gamma$ be a variable context, $S$ a store
typing and $\mu$ a store that is well typed under $\Gamma$ and $S$. If $v$ is a value of type
$T$ under $\Gamma$ and $S$, then the store obtained by appending $v$ at the end of $\mu$ is well
typed under $\Gamma$ and the store typing obtained by appending $T$ at the end of $S$.
