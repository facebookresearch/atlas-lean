# Matroids

A matroid on a type $\alpha$ is a ground set $E \subseteq \alpha$ with a nonempty family of subsets of $E$, its bases, satisfying the basis exchange property and the maximality property; its independent sets are the subsets of bases.

A *matroid* $M$ on a type $\alpha$ consists of a set $E \subseteq \alpha$, the *ground set*, a predicate $\mathrm{IsBase}$ on subsets of $\alpha$ (the *bases*) and a predicate $\mathrm{Indep}$ on subsets of $\alpha$ (the *independent sets*) such that:

1. a set $I$ is independent exactly when $I \subseteq B$ for some base $B$;
2. there is at least one base;
3. for bases $B, B'$ and $e \in B \setminus B'$ there is $f \in B' \setminus B$ such that $(B \setminus \{e\}) \cup \{f\}$ is a base;
4. for every $X \subseteq E$, every independent subset $I$ of $X$ is contained in a maximal independent subset of $X$;
5. every base is contained in $E$.

The matroid is *finite* when $E$ is finite. For a finite matroid the rank of a set $X$ (Mathlib's `Matroid.eRk`, the size of a largest independent subset of $X$) satisfies $r(X) \le |X|$, is monotone and is submodular, $r(X \cup Y) + r(X \cap Y) \le r(X) + r(Y)$; a finite set $I$ is independent exactly when $r(I) = |I|$. These are the rank axioms by which Kühne and Yashfe define a matroid $M = (E, r)$ on a finite ground set, and a finite matroid can be given to an algorithm by the table of its rank function.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Definition 2.1 of arXiv:2206.03465v3 (matroids given by rank functions).
