# Dickson's lemma for finite products of well-quasi-orders

Let $\iota$ be a finite type and, for each $i \in \iota$, let $\alpha_i$ be a preorder that is well-quasi-ordered by $\le$: every sequence $f : \mathbb{N} \to \alpha_i$ has indices $m < n$ with $f(m) \le f(n)$. Then the product $\prod_{i \in \iota} \alpha_i$, ordered componentwise, is well-quasi-ordered by $\le$. With $\iota = \{1, \dots, k\}$ and every $\alpha_i = \mathbb{N}$ this is the statement that every infinite sequence of vectors in $\mathbb{N}^k$ has two terms $A_m \le A_n$ with $m < n$.

## Sources

- The mathlib Community, *mathlib4* at revision fc4f59e577, `Pi.wellQuasiOrderedLE`, <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577/Mathlib/Order/WellQuasiOrder.lean#L210-L214>.
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Lemma 3.2.2 (Dickson's lemma for $\mathbb{N}^k$), p. 49.
