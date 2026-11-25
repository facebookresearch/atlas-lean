# Hindley–Milner typing is stable under type substitution

Let $\Gamma$ be a typing
context, $e$ an expression and $\tau$ a monotype with $\Gamma \vdash e : \tau$. Then for every
type substitution $s$, $s\Gamma \vdash e : s\tau$, where $s\Gamma$ applies $s$ to every scheme of
$\Gamma$ and $s\tau$ applies $s$ to $\tau$.
