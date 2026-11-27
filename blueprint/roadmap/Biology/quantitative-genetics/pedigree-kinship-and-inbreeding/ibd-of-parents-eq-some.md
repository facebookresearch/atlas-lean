# Malécot's recursion step for identity by descent

In a [pedigree](pedigree.md), let $i, j$ be individuals with $j \ne i$, $j$ not an [ancestor](is-ancestor.md) of $i$, and $j$ a non-founder with parents $p_0 = f(j)$, $p_1 = m(j)$. Then for all $a, b \in \{0, 1\}$,

$$\mathrm{IBD}\bigl((i, a), (j, b)\bigr) = \frac12\Bigl(\mathrm{IBD}\bigl((i, a), (p_b, 0)\bigr) + \mathrm{IBD}\bigl((i, a), (p_b, 1)\bigr)\Bigr),$$

where $\mathrm{IBD}$ is the [probability of identity by descent](ibd.md).
