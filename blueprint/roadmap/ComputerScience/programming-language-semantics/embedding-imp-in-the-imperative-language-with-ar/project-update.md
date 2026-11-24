# Projection commutes with updates under an injective renaming

Let $\rho$ be an injective renaming from natural numbers to strings. For every state $s$ of the imperative language with arrays and all natural numbers $n$ and $v$,

$$\pi_\rho\big(s[\rho(n) \mapsto v]\big) = \pi_\rho(s)[n \mapsto v],$$

where $\pi_\rho$ is the projection onto IMP states and the right-hand side updates the IMP state at the variable $x_n$.
