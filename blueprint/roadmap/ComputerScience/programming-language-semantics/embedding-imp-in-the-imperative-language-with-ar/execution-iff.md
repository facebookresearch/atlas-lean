# Execution correspondence between IMP and its translation under an injective renaming

Let $\rho$ be an injective renaming from natural numbers to strings, $c$ an IMP command, $s$ a state of the imperative language with arrays and $f$ an IMP state. Then $c$ takes $\pi_\rho(s)$ to $f$ in the big-step semantics of IMP if and only if there is a state $t$ such that the translation of $c$ takes $s$ to $t$ and $\pi_\rho(t) = f$.
