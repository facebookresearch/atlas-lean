# Editing a digraph to a binary-explainable BMG is NP-complete

Let $(\vec G,\sigma)$ be a properly vertex-colored digraph on the gene set $L$, with colors denoting species. It is a **best match graph (BMG)** if some leaf-colored tree $(T,\sigma)$ *explains* it: $(x,y)$ is an arc iff $\sigma(x)\ne\sigma(y)$ and $y$ is a closest relative of $x$ in $T$ (minimal last common ancestor) among the genes of color $\sigma(y)$. The graph is **sf-colored** (sink-free) if every vertex has an out-neighbor of every other color. Its **informative** and **forbidden** triples are

$$\mathscr{R}=\{ab|b':\sigma(a)\ne\sigma(b)=\sigma(b'),\ (a,b)\in E,\ (a,b')\notin E\},\qquad \mathscr{F}=\{ab|b':\sigma(a)\ne\sigma(b)=\sigma(b'),\ b\ne b',\ (a,b),(a,b')\in E\}.$$

**Problem ($\ell$-BMG EBEG).** Given a properly $\ell$-colored digraph $(\vec G=(V,E),\sigma)$ and an integer $k$, decide whether there is a set $F$ of non-loop arcs with $|F|\le k$ such that $(V,E\,\triangle\,F)$ with coloring $\sigma$ is a binary-explainable $\ell$-BMG. The deletion-only variant (DBEG) requires $F\subseteq E$, the completion-only variant (CBEG) requires $F\cap E=\emptyset$.

**Theorem.** $2$-BMG EBEG and $2$-BMG DBEG are NP-complete, and $\ell$-BMG EBEG and $\ell$-BMG DBEG are NP-complete for every $\ell\ge 2$. (Completion, CBEG, was known to be NP-complete for $\ell\ge 2$.) This corrects Theorem 5 of the source, which prints "$\ell$-BMG EBEG and 2-BMG DBEG are NP-complete for all $\ell\ge2$"; the clause for $\ell$-BMG DBEG is what, in the source's words, its Theorem 4 and Corollary 4 together with Remark 6.3 of its reference [19] immediately imply. All three problems admit exact integer linear programming formulations that add the consistency constraints of the extended triple set $\mathscr{R}_{\mathrm{bin}}$ to the BMG-modification ILP.

## Depends on

- [Binary-explainable BMGs are characterized by consistency of the extended informative triples](binary-explainable-bmgs-are-characterized-by-consistency-of-the-extended-informative-triples.md)

## Expansion

Membership in NP follows from polynomial-time recognition of binary-explainable BMGs via consistency of $\mathscr{R}_{\mathrm{bin}}$. Hardness is by reduction from Exact 3-Cover: a modification of the gadget used for general BMG editing produces instances whose optimally edited graphs are already binary-explainable, and the optimal edit set consists only of arc deletions, which gives the deletion result too. Padding with extra colors lifts the $\ell=2$ result to every $\ell\ge2$.

## Sources

- David Schaller, Manuela Geiß, Marc Hellmuth and Peter F. Stadler, "Best Match Graphs with Binary Trees", arXiv:2011.00511 (2020), Problem 1, Theorems 4–5, Corollary 4 and Section 6 (ILP formulation), <https://doi.org/10.48550/arXiv.2011.00511>.
