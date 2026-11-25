# Table invariants preserved by lazy runs

Let $I$ be a property of tables that survives recording any possible fresh answer: if $I(T)$ holds,
$T$ records no answer to $x$, and $y$ lies in the support of $\nu_T(x)$, then $I$ holds for $T$
extended by $x \mapsto y$. Then on every run of an oracle computation against the lazily sampled
oracle from a table satisfying $I$, the final table satisfies $I$.
