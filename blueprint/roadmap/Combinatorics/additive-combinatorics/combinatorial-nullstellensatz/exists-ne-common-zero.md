# Chevalley–Warning theorem, existence form

Let $K$ be a finite field, $\sigma$ a finite set of variables, and $f_j \in K[x_i : i \in \sigma]$
for $j$ in a finite index set $J$. If

$$\sum_{j \in J} \deg f_j < |\sigma|$$

and the $f_j$ have a common zero $x \in K^\sigma$, then they have a common zero $y \in K^\sigma$ with
$y \ne x$.

Alon states this over the prime fields $\mathbb{Z}_p$ and proves it with Theorem 1.2; for an
arbitrary finite field it also follows from the Chevalley–Warning divisibility theorem, which says
that the number of common zeros is divisible by the characteristic of $K$.

## Informally uses

- [Combinatorial Nullstellensatz, Theorem 1.2](exists-eval-ne-zero.md): the paper's proof applies it to $\prod_i (1 - P_i^{p-1}) - \delta \prod_j \prod_{c \ne c_j} (x_j - c)$ on the grid $\mathbb{Z}_p^n$.

## Sources

- Noga Alon, "Combinatorial Nullstellensatz", *Combin. Probab. Comput.* 8 (1999) 7–29, Theorem 3.1.
