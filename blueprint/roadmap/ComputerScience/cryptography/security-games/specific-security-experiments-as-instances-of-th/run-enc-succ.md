# Dropping the first entry of the up-front randomness

Let $Y$ be an additive commutative group, $f \colon X \to Y$ and $\rho \in X^{n+1}$. For every oracle computation $c$ and index $i$, running $c$ with $\mathrm{runEnc}$ and tape $\rho$ from index $i + 1$ equals running $c$ with the tail $(\rho_1, \dots, \rho_n)$ from index $i$ and then changing a result `some` $(a, j)$ to `some` $(a, j + 1)$; a result `none` is left unchanged.

Here $\mathrm{runEnc}$ runs an oracle computation against the encryption oracle with up-front randomness $\rho \in X^q$, starting from a query index $i$: a returned value $a$ gives `some` $(a, i)$; a query $m$ with $i < q$ is answered by $(\rho_i, f(\rho_i) + m)$ and the run continues from index $i + 1$; a query with $i \ge q$ makes the run fail (`none`).

No finiteness hypothesis is needed.
