# The chase for inclusion dependencies

An inclusion dependency $\sigma = R[i_1, \dots, i_m] \subseteq P[j_1, \dots, j_m]$, with $m \ge 1$, distinct positions $i_1, \dots, i_m$
of $R$ and distinct positions $j_1, \dots, j_m$ of $P$, holds in a possibly infinite database $D$ if for every tuple
$\bar a \in R^D$ there is $\bar b \in P^D$ with $(a_{i_1}, \dots, a_{i_m}) = (b_{j_1}, \dots, b_{j_m})$.

For an atom $R(\bar u)$ in a set of atoms $S$, let $\mathrm{new}(\sigma, \bar u)$ be the atom $P(v_1, \dots, v_{\mathrm{ar}(P)})$
with $v_{j_k} = u_{i_k}$ for $k \in [m]$ and, at every other position $\ell$, a fresh variable determined by $\sigma$, $\ell$ and
$(u_{i_1}, \dots, u_{i_m})$ alone. The dependency $\sigma$ is *applicable* to $S$ with $\bar u$ when $R(\bar u) \in S$ and
$\mathrm{new}(\sigma, \bar u) \notin S$; applying it adds $\mathrm{new}(\sigma, \bar u)$.

A finite chase sequence of $S$ under a set $\Sigma$ of inclusion dependencies is $S = S_0, \dots, S_n$ where each step applies an
applicable dependency and none is applicable to $S_n$; its result is $S_n$. An infinite chase sequence $S_0, S_1, \dots$ applies
an applicable dependency at each step and is fair: every dependency applicable to some $S_i$ with some $\bar u$ has added
$\mathrm{new}(\sigma, \bar u)$ by some later $S_j$; its result is $\bigcup_i S_i$. The common result of all chase sequences
(see [uniqueness](the-ind-chase-has-a-unique-result.md)) is written $\mathrm{Chase}(S, \Sigma)$. For example, the chase of
$\{R(a, b)\}$ under $R[2] \subseteq R[1]$ is infinite.

## Depends on

- [Inclusion dependencies and finite implication](../inclusion-dependencies-and-finite-implication.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 11.2, 11.3 and 11.5 and the example after Definition 11.5 (pp. 77–80).
