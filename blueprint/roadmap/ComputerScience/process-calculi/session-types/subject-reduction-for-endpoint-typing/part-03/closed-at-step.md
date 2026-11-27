# Reduction steps preserve process scoping

Let $p$, $q$ be processes with $p \to q$ and $n$ a natural number. If $p$ is scoped at depth $n$
(every variable under $m$ binders has index $< n + m$), then so is $q$.
