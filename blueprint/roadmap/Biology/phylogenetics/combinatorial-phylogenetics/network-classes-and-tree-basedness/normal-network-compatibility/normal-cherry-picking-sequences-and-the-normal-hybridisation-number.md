# Normal cherry-picking sequences and the normal hybridisation number

**Setting.** A rooted phylogenetic network $\mathcal{N}$ on $X$ is **tree-child** if every non-leaf vertex has a child that is a leaf or a tree vertex, and **normal** if it is tree-child and has no **shortcut**, i.e. no reticulation edge $(u,v)$ such that $\mathcal{N}$ also has a directed path from $u$ to $v$ avoiding $(u,v)$. A set $\mathcal{P}$ of rooted phylogenetic $X$-trees is **normal compatible** if some normal network displays every tree in $\mathcal{P}$. With $h(\mathcal{N}) = \sum_{v \ne \rho}(d^-(v) - 1)$, let $h_{\mathrm{n}}(\mathcal{P})$ and $h_{\mathrm{tc}}(\mathcal{P})$ be the minimum of $h(\mathcal{N})$ over normal, respectively tree-child, networks displaying $\mathcal{P}$.

A **tree-child cherry-picking sequence** for $\mathcal{P}$ is a sequence $\sigma = (x_1,y_1),\dots,(x_s,y_s),(x_{s+1},-)$ with $x_i \notin \{y_{i+1},\dots,y_s\}$ for all $i \le s$ such that cherry picking the pairs in order (deleting $x_i$ from every tree in which $\{x_i,y_i\}$ is a cherry) reduces every tree to the single leaf $x_{s+1}$; its weight is $w(\sigma) = s + 1 - |X|$. A string of pairs $(x_1,y_1),\dots,(x_s,y_s)$ is a **shortcut sequence** if there are indices $1 = i_1 < \dots < i_m = s$ with either $m = 2$ and $(x_{i_1},y_{i_1}) = (x_{i_2},y_{i_2})$, or $m > 2$, $x_{i_1} = x_{i_m}$, $x_{i_1} \notin \{x_{i_j},y_{i_j}\}$ for $1 < j < m$, the $x_{i_2},\dots,x_{i_{m-1}}$ are distinct, and consecutive selected pairs share an element. The sequence $\sigma$ is a **normal cherry-picking sequence** if no substring $\sigma[i,j]$ with $i < j$ is a shortcut sequence. Let $s(\mathcal{P})$ be the minimum weight of a normal cherry-picking sequence for $\mathcal{P}$.

**Theorem.**

1. $\mathcal{P}$ is normal compatible if and only if it has a normal cherry-picking sequence, and then $h_{\mathrm{n}}(\mathcal{P}) = s(\mathcal{P})$.
2. Any two rooted phylogenetic $X$-trees (binary or not) are normal compatible.
3. This fails for three trees: the three binary trees on $\{a,b,c\}$ are not displayed by any normal network.
4. For caterpillars $\mathcal{T}_1 = (\ell_1,\ell_2,\dots,\ell_n)$ and $\mathcal{T}_2 = (\ell_2,\ell_3,\dots,\ell_n,\ell_1)$ with $n \ge 3$,

$$h_{\mathrm{tc}}(\mathcal{T}_1,\mathcal{T}_2) = 1, \qquad h_{\mathrm{n}}(\mathcal{T}_1,\mathcal{T}_2) = n - 2,$$

so the cost of forbidding shortcuts can be as large as the maximum possible number $|X| - 2$ of reticulations in a binary normal network.

## Depends on

- [Hybridisation number equals the minimum weight of a leaf-added cherry-picking sequence](../leaf-added-cherry-picking-sequences/hybridisation-number-equals-minimum-leaf-added-cherry-picking-weight.md)

## Expansion

Reading a tree-child cherry-picking sequence backwards constructs a tree-child network displaying $\mathcal{P}$ with $w(\sigma)$ reticulations; a repeated pair, or a chain of pairs linked by shared leaves that returns to the same first element, is exactly what makes the newly added reticulation edge parallel to an existing directed path, i.e. a shortcut. Forbidding such substrings therefore yields a normal network, giving $h_{\mathrm{n}} \le s$. Conversely a normal network displaying $\mathcal{P}$ can be reduced by cherries and reticulated cherries in an order whose sequence inherits the absence of shortcuts, giving $h_{\mathrm{n}} \ge s$. For three trees on three leaves the obstruction is counting: a binary normal network with $k$ reticulations displays exactly $2^k$ binary trees and has at most $|X| - 2$ reticulations, and a single reticulation of in-degree three on three leaves always creates a shortcut. For two trees one builds a normal network inductively along a common cherry-picking order, adding at most one reticulation per picked leaf.

## Sources

- Magnus Bordewich, Simone Linz and Charles Semple, "When is a set of phylogenetic trees displayed by a normal network?", arXiv:2407.06638 (2024), Theorem 4.2, Corollary 4.3, Theorem 5.7 and the disparity proposition of Section 6, <https://doi.org/10.48550/arXiv.2407.06638>. Published version: Journal of Computer and System Sciences 160 (2026) 103811, <https://doi.org/10.1016/j.jcss.2026.103811>.
