# Recombination vector for degree-2t sharings

Let $F$ be a field, $\mathrm{Party}$ a finite type, $\alpha : \mathrm{Party} \to F$ injective and $t \in \mathbb{N}$. If $2t < |\mathrm{Party}|$, there is a single vector $r : \mathrm{Party} \to F$, independent of the polynomial, such that every polynomial $p$ over $F$ of natural degree at most $2t$ satisfies

$$
p(0) = \sum_{i \in \mathrm{Party}} r_i \, p(\alpha_i).
$$

One such vector is given by the Lagrange basis on the points $\alpha_i$ evaluated at $0$. These weights reconstruct $p(0)$ and are used in the BGW multiplication step; they are not the whole step, which also re-shares each local product and so reduces the degree from $2t$ back to $t$ (Ben-Or, Goldwasser and Wigderson, STOC 1988, p. 4).
