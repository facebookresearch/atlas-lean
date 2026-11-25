# Deletion stability bounds replacement stability

If an algorithm $A$ has uniform (deletion) stability $\beta$ with respect to $\ell$, then for every sample $S$ of size $m$, every $i$, every replacement point $z'$ and every $z$,
$\lvert \ell(A_S, z) - \ell(A_{S^{i}}, z) \rvert \le 2\beta$, where $S^{i}$ is $S$ with its $i$-th point replaced by $z'$.

## Proof

Removing the $i$-th point from $S$ and from $S^{i}$ gives the same sample $S \setminus i$, so by the triangle inequality
$\lvert \ell(A_S, z) - \ell(A_{S^i}, z) \rvert \le \lvert \ell(A_S, z) - \ell(A_{S \setminus i}, z) \rvert + \lvert \ell(A_{S \setminus i}, z) - \ell(A_{S^i}, z) \rvert \le 2\beta$.

## Depends on

- [Uniform stability implies high-probability generalization](uniform-stability-implies-high-probability-generalization.md)

## Sources

- O. Bousquet and A. Elisseeff, *Stability and generalization*, JMLR 2 (2002). Background reference.
