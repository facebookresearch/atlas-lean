# Payload substitution at any cutoff preserves session typing

Let $n$, $k$ be natural numbers with $k \le n$, $\Gamma$ a session context, $p$ a process and $b$ a
name in scope at depth $n$ (a free constant, or a variable with index $< n$). If $\Gamma
\vdash_{n+1} p$, then $\Gamma \vdash_n p\{b/k\}$, where $p\{b/k\}$ replaces the variable with index
$k$ by $b$, leaves smaller indices unchanged, lowers larger indices by one, and under each binder
raises the cutoff by one and lifts the free variables of $b$ by one.
