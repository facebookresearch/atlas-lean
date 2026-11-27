# IMP executions lift to executions of translated commands under an injective renaming

Let $\rho$ be an injective renaming from natural numbers to strings, and let the IMP command $c$ take the IMP state $i$ to the IMP state $f$ in the big-step semantics of IMP. Then for every state $s$ of the imperative language with arrays with $\pi_\rho(s) = i$ there is a state $t$ such that the translation of $c$ takes $s$ to $t$ in the big-step semantics and $\pi_\rho(t) = f$.
