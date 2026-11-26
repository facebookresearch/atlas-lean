# Session-typed threads are well scoped

Let $n$ be a natural number, $\Gamma$ a session context and $p$ a process. If $\Gamma \vdash_n p$,
then $p$ is scoped at depth $n$: every de Bruijn variable occurring in $p$ under $m$ binders (inputs
and restrictions) of $p$ has index $< n + m$. Free channel constants may occur.
