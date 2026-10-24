---
article_id: af_bdcdd87277d2e8419febc725
declaration: def
origin: cited
statement: formalized
lean: UniqueGames.StrongUGC
---

# Definition 1.4 (A strongish form of UGC)

For $\eta > 0$, $t \in \mathbb{N}$ we are given a non-bipartite Unique-Games instance $\Psi = (X, E, \Sigma, \Phi)$, and we wish to distinguish between the following two cases: 1. YES case: there exists $X'' \subseteq X$ of size at least $(1 - \eta)|X|$, and an assignment $A \colon X'' \to \Sigma$, such that $A$ satisfies all of the constraints inside $X''$. 2. NO case: for all $X'' \subseteq X$ of size at least $\eta |X|$ and a $t$-assignment, i.e. $A \colon X'' \to \binom{\Sigma}{t}$, not all of the constraints in $X''$ are satisfied by $A$.

## Depends on

- [Definition 3.5 (Lecture 15, Section 3.2)](../lecture-15/094-definition-3-5.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Lecture 17, Section 1.3](../../../../sources/v1/BooleanFunctions.md)
