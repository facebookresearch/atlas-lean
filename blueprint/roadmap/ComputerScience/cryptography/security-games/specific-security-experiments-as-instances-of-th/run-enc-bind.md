# Up-front encryption randomness under sequential composition

Let $Y$ be an additive commutative group, $f \colon X \to Y$, $\rho \in X^q$, $c$ an oracle computation and $g$ a continuation. For every starting index $i$, running the sequential composition $c \mathbin{>\!\!>\!\!=} g$ with $\mathrm{runEnc}$ from $i$ equals: run $c$ from $i$; if that fails, the result is `none`; if it returns `some` $(a, j)$, run $g(a)$ from index $j$.

Here $\mathrm{runEnc}$ runs an oracle computation against the encryption oracle with up-front randomness $\rho \in X^q$, starting from a query index $i$: a returned value $a$ gives `some` $(a, i)$; a query $m$ with $i < q$ is answered by $(\rho_i, f(\rho_i) + m)$ and the run continues from index $i + 1$; a query with $i \ge q$ makes the run fail (`none`).

No finiteness hypothesis is needed.
