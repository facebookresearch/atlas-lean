# Tree iterations with the equal-level relation

The weak and strong tree iterations of a relational structure $\mathcal{M}$ are trees on the set $M^*$ of finite words over its domain, with the relations of $\mathcal{M}$ copied among the children of each node; the strong iteration adds a clone predicate, and the equal-level relation links nodes of the same depth. Chain logic restricts set quantifiers to subsets of paths.

**Tree iterations.** Let $\mathcal{M} = (M, R_1, \dots, R_k)$ be a relational structure with finite signature. Its *weak tree iteration* is

$$
\mathcal{M}^\# = (M^*, \preceq, S, R_1^*, \dots, R_k^*),
$$

where $u \preceq v$ iff $u$ is a prefix of $v$, $S = \{(u, um) : u \in M^*, m \in M\}$, and for $\ell$-ary $R_i$, $R_i^*(v_1, \dots, v_\ell)$ is true iff $v_j = z m_j$ for some $z \in M^*$, $m_1, \dots, m_\ell \in M$ with $R_i(m_1, \dots, m_\ell)$. The *strong tree iteration* $\mathcal{M}^*$ adds the *clone predicate* $C = \{umm : u \in M^*, m \in M\}$. Adding the *equal-level relation* $E(u,v) \iff |u| = |v|$ gives $\mathcal{M}^\#_E$ and $\mathcal{M}^*_E$.

**Chain logic.** A *path* is a maximal set of nodes linearly ordered by $\preceq$, and a *chain* is a subset of a path. *Chain logic* is monadic second-order logic over these tree structures with set quantifiers restricted to chains. For a logic $\mathcal{L}$, *chain logic with $\mathcal{L}$ on siblings* additionally allows $\mathcal{L}$-quantifiers ranging over the set of children $\{zm : m \in M\}$ of a node $z$; *MSO on tree levels* instead allows monadic second-order quantifiers over subsets of a single level $\{v : |v| = n\}$. The *theory* of a structure in such a logic is the set of its sentences true in the structure.

**Binary tree.** For $\mathcal{M}_2 = (\{0,1\}, \{0\}, \{1\})$ the weak and strong iterations are interdefinable (the clone predicate is definable when $M$ is finite), and $\mathcal{M}^\#_{2,E}$ is the binary tree with the equal-level relation.

## Depends on

None.

## Proof depends on

None.

## Expansion

Shelah–Stupp (weak) and Muchnik–Walukiewicz (strong) proved that monadic second-order logic over the iteration is decidable when it is decidable over $\mathcal{M}$. With $E$ the full monadic theory of the binary tree becomes undecidable, but its chain theory is decidable (Thomas). The source proves that the chain theory of $\mathcal{M}^\#_E$ with $\mathcal{L}$ on siblings is decidable whenever the $\mathcal{L}$-theory of $\mathcal{M}$ is (for admissible $\mathcal{M}$, which has two singleton predicates naming elements $0$ and $1$), by coding chains as $\omega$-words over $M \times \{0,1\}$ and using Büchi automata whose transitions are given by $\mathcal{L}$-formulas.

## Sources

- Alex Spelten, Wolfgang Thomas and Sarah Winter, "Trees over infinite structures and path logics with synchronization", in *Proceedings 13th International Workshop on Verification of Infinite-State Systems (INFINITY 2011)*, Electronic Proceedings in Theoretical Computer Science 73, 2011, pp. 20–34, doi:10.4204/EPTCS.73.5; read as arXiv:1111.3107v1, <https://arxiv.org/abs/1111.3107v1>: Section 2 (tree iterations, the clone predicate, the equal-level relation and chain logic), Section 1 (siblings and history) and Theorem 12 of arXiv:1111.3107v1.
