# Removing redundant atoms computes a core

Let $q(\bar x)$ be a conjunctive query. Start with $S = A_q$ and, while some atom $R(\bar u) \in S$ is such that every
variable of $\bar x$ occurs in $S \setminus \{R(\bar u)\}$ and $(S, \bar x) \to (S \setminus \{R(\bar u)\}, \bar x)$, remove
one such atom from $S$. This procedure terminates after at most $|A_q|$ removals, whatever atoms it chooses, and the
conjunctive query with head $\bar x$ and body the final $S$ is a [core](minimizations-and-cores-of-conjunctive-queries.md)
of $q$. Different choices can give syntactically different cores.

## Depends on

- [Minimizations and cores of conjunctive queries](minimizations-and-cores-of-conjunctive-queries.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Algorithm 4 (ComputeCore) and Lemma 16.6 (pp. 126–127).
