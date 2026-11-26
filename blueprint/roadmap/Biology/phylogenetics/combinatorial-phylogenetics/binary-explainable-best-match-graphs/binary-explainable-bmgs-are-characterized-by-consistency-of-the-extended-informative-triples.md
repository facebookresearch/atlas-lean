# Binary-explainable BMGs are characterized by consistency of the extended informative triples

Let $(\vec G,\sigma)$ be a properly vertex-colored digraph on the gene set $L$, with colors denoting species. It is a **best match graph (BMG)** if some leaf-colored tree $(T,\sigma)$ *explains* it: $(x,y)$ is an arc iff $\sigma(x)\ne\sigma(y)$ and $y$ is a closest relative of $x$ in $T$ (minimal last common ancestor) among the genes of color $\sigma(y)$. The graph is **sf-colored** (sink-free) if every vertex has an out-neighbor of every other color. Its **informative** and **forbidden** triples are

$$\mathscr{R}=\{ab|b':\sigma(a)\ne\sigma(b)=\sigma(b'),\ (a,b)\in E,\ (a,b')\notin E\},\qquad \mathscr{F}=\{ab|b':\sigma(a)\ne\sigma(b)=\sigma(b'),\ b\ne b',\ (a,b),(a,b')\in E\}.$$

A BMG is **binary-explainable** if a binary (fully resolved) tree explains it. Define the extended informative triple set

$$\mathscr{R}_{\mathrm{bin}}(\vec G,\sigma)=\mathscr{R}(\vec G,\sigma)\cup\{bb'|a:\ ab|b'\in\mathscr{F}(\vec G,\sigma),\ \sigma(b)=\sigma(b')\}.$$

**Theorem.** A properly colored digraph $(\vec G,\sigma)$ is binary-explainable if and only if (i) it is sf-colored and (ii) $\mathscr{R}_{\mathrm{bin}}$ is consistent (displayed by some tree). In that case every refinement of the Aho tree $\mathrm{Aho}(\mathscr{R}_{\mathrm{bin}},L)$ explains $(\vec G,\sigma)$, and a binary explaining tree can be constructed, or its nonexistence certified, in $O(|L|^3\log^2|L|)$ time.

**Binary-refinable tree.** For a binary-explainable BMG, the *binary-refinable tree* (BRT) is $(\mathrm{Aho}(\mathscr{R}_{\mathrm{bin}},L),\sigma)$. It refines the unique least resolved tree, every tree displaying $\mathscr{R}_{\mathrm{bin}}$ refines it, and a binary tree explains the BMG **iff** it is a refinement of the BRT. Hence, if gene families evolve only by bifurcations and the BMG is correct, the true gene tree displays the BRT.

## Expansion

In a binary tree, two genes $b,b'$ of the same color that are both best matches of $a$ must lie in a common subtree not containing $a$, so the forbidden triple $ab|b'$ forces the resolved triple $bb'|a$; this is why binary explanations display $\mathscr{R}_{\mathrm{bin}}$. Conversely, a tree displaying $\mathscr{R}_{\mathrm{bin}}$ displays all informative triples and, displaying $bb'|a$, cannot display the forbidden $ab|b'$, so the pair $(\mathscr{R},\mathscr{F})$ is consistent and the general triple characterization of BMGs applies. The BRT is the least resolved tree for $\mathscr{R}_{\mathrm{bin}}$, and since the closure of $\mathscr{R}_{\mathrm{bin}}$ equals the triple set of the BRT, $\mathscr{R}_{\mathrm{bin}}$ identifies it.

## Sources

- David Schaller, Manuela Geiß, Marc Hellmuth and Peter F. Stadler, "Best Match Graphs with Binary Trees", arXiv:2011.00511 (2020), Proposition 1, Theorem 1, Corollaries 1 and 3, Theorem 2 and Section 4 (binary-refinable tree), <https://doi.org/10.48550/arXiv.2011.00511>.
