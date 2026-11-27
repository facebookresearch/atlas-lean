# The chase for functional dependencies on sets of atoms

Fix a strict total order on constants and variables in which every constant precedes every variable and which is
decidable in polynomial time on the encodings of the terms (for example, constants before variables, and lexicographic
order on encodings within each kind). Let $S$ be a finite set
of atoms over a schema, with constants and variables, and $\Sigma$ a set of functional dependencies $R : U \to V$ over it,
where $U, V$ are sets of positions of $R$. A dependency $R : U \to V$ is *applicable* to $S$ with atoms $R(\bar u), R(\bar v) \in S$
and a position $i \in V$ when $\pi_U(\bar u) = \pi_U(\bar v)$ and $u_i \ne v_i$. Applying it fails, with result $\bot$, if $u_i$
and $v_i$ are distinct constants; otherwise it replaces every occurrence in $S$ of the larger of $u_i, v_i$ by the smaller
one. Applying $R : U \to V$ one position at a time is applying the functional dependencies $R : U \to \{i\}$, $i \in V$,
which together are equivalent to it; a step on several positions at once need not be a function: for
$R(k, a, b), R(k, x, x)$ and $\{1\} \to \{2, 3\}$ it would send $x$ to both $a$ and $b$, whereas position by position it
maps $x$ to $a$ and then fails on $a, b$.

A chase sequence of $S$ under $\Sigma$ is a finite sequence $S = S_0, S_1, \dots, S_n$ in which each $S_{i+1}$ is obtained from
$S_i$ by one application and which ends in failure or saturation: it is *failing* if $S_n = \bot$ and *successful* if no
dependency of $\Sigma$ is applicable to $S_n$. A run is a finite or infinite sequence $S_0 = S, S_1, \dots$ in which each
$S_{i+1}$ is obtained from $S_i$ by one application; a finite run that stops earlier is partial, not a chase sequence: for
$R(k, x), R(k, y)$ and $1 \to 2$ the zero-step prefix is partial, and only the run that identifies $x$ and $y$ is a chase
sequence.
The composition of the replacement maps along a successful sequence is its chase homomorphism. When all finite chase
sequences end in the same result (see [termination and uniqueness](the-fd-chase-terminates-with-a-unique-result.md)), that
result is written $\mathrm{Chase}(S, \Sigma)$; $h_{S, \Sigma}$ denotes the chase homomorphism of a fixed successful
sequence, and the statements that use it hold for every such choice, since all of them have the same image
$h_{S, \Sigma}(S) = \mathrm{Chase}(S, \Sigma)$; a use of $h_{S, \Sigma}$ on individual terms refers to that fixed choice.

## Depends on

- [Functional dependency](../../functional-dependencies/fd.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 10.2, 10.3 and 10.5 and the definition of the chase homomorphism (pp. 70–73).
