# Energy of the loop closed by a base pair

For a [loop energy model](loop-energy.md), a finite set $P$ of pairs and a pair $p = (i, j)$ with branches $\beta$ (the [branches](branches.md) of $p$ in $P$), the loop energy is

- $H(i, j)$ if $p$ has no branch;
- $I(i, j, k, l)$ if $(k, l)$ is the only branch;
- $a + b\,|\beta| + c\,u$ if $p$ has at least two branches, where $u = \max\bigl(j - i - 1 - \sum_{(k, l) \in \beta} (\max(l - k, 0) + 1),\ 0\bigr)$; for a secondary structure $P$ containing $p$, $u$ is the number of unpaired bases in the loop closed by $p$.
