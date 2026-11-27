# The chase for functional dependencies on sets of atoms

Fix a strict total order on constants and variables in which every constant precedes every variable. Let $S$ be a finite set
of atoms over a schema, with constants and variables, and $\Sigma$ a set of functional dependencies $R : U \to V$ over it,
where $U, V$ are sets of positions of $R$. A dependency $R : U \to V$ is *applicable* to $S$ with atoms $R(\bar u), R(\bar v) \in S$
when $\pi_U(\bar u) = \pi_U(\bar v)$ and $\pi_V(\bar u) \ne \pi_V(\bar v)$. Applying it fails, with result $\bot$, if some position
of $V$ carries two distinct constants; otherwise it replaces, everywhere in $S$, the larger of each pair of distinct terms
$u_i, v_i$ at positions of $V$ by the smaller one.

A finite chase sequence of $S$ under $\Sigma$ is a sequence $S = S_0, S_1, \dots, S_n$ in which each $S_{i+1}$ is obtained from
$S_i$ by one application; it is *failing* if $S_n = \bot$ and *successful* if no dependency of $\Sigma$ is applicable to $S_n$.
The composition of the replacement maps along a successful sequence is its chase homomorphism. When all finite chase
sequences end in the same result (see [termination and uniqueness](the-fd-chase-terminates-with-a-unique-result.md)), that
result is written $\mathrm{Chase}(S, \Sigma)$ and the chase homomorphism $h_{S, \Sigma}$.

## Depends on

- [Functional dependency](../../functional-dependencies/fd.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 10.2, 10.3 and 10.5 and the definition of the chase homomorphism (pp. 70–73).
