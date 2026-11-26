# Shape polynomial of genus-g topological RNA structures

**Setting.** An RNA diagram is a set of arcs (base pairs, possibly crossing) on backbone vertices $1,\dots,n$, each vertex in at most one arc. Thickening the backbone and arcs into ribbons gives a fatgraph; collapsing the backbone to one vertex, a diagram with $e$ arcs and $b$ boundary components has genus $g$ with $2-2g=1-e+b$. Arc $(i,i+1)$ is a *1-arc*; arcs $(i,j)$ and $(i+1,j-1)$ are *parallel*. A *shape* is a diagram with no 1-arcs and no parallel arcs, with a rainbow arc enclosing everything; the shape of a structure is obtained by collapsing every stack to a single arc, deleting 1-arcs and repeating, so shapes are the homotopy classes of arc configurations. Let $\eta_g(n,0)$ be the number of shapes of genus $g$ with $n$ arcs and $S_g(z)=\sum_n\eta_g(n,0)z^n$.

**Theorem.** For $g\ge1$, with the unicellular-map coefficients $\kappa^{(g)}_t=a^{(g)}_t\,\mathrm{Cat}(2g+t)$,

$$S_g(z)=\sum_{t=0}^{g-1}\kappa^{(g)}_t\,z^{2g+t}(1+z)^{2g+t}.$$

In particular $S_g$ is a polynomial: for fixed genus there are finitely many shapes, every shape of genus $g$ has between $2g$ and $6g-2$ arcs, and $\eta_g(n,0)=\sum_{t=0}^{g-1}a^{(g)}_t\binom{2g+t}{n-2g-t}\mathrm{Cat}(2g+t)$. For $g=1$, $S_1(z)=z^2(1+z)^2=z^2+2z^3+z^4$: four genus-one shapes, with two, three, three and four arcs. Moreover, choosing $t$ with probability proportional to $a^{(g)}_t\eta_0(n,2g+t+1)$ and then gluing a uniformly random planar shape gives a uniform random generator of genus-$g$ shapes with $n$ arcs.

## Expansion

Every vertex of the unicellular map dual to a shape has degree at least $3$, since a degree-one vertex would be a 1-arc and a degree-two vertex a pair of parallel arcs (the rainbow rules out the remaining case). Shapes therefore correspond to unicellular maps without low-degree vertices, and the trisection recursion reduces genus-$g$ shapes to planar (genus-$0$) shapes with $k=2g+t+1$ labelled vertices, counted by $\eta_0(n,k)$. For these, Rémy's bijection gives $(2k-n-2)\eta_0(n,k)=(n+1-k)\eta_0(n+1,k)$ and hence $\eta_0(n,k)=\binom{k-1}{n+1-k}\mathrm{Cat}(k-1)$; summing with the weights $a^{(g)}_t$ yields the polynomial. Finiteness of shapes per genus is what makes topological folding algorithms that enumerate structures of bounded genus run in polynomial time, and uniform shape generation supports sampling-based studies of pseudoknot topology.

## Depends on

- [Generating function of unicellular maps of genus g](unicellular-map-generating-function-of-genus-g.md)

## Sources

- F. W. D. Huang, C. M. Reidys, "Shapes of topological RNA structures", arXiv:1403.2908 (2014), Section "Some basic facts" (Proposition 1), Section "Shapes of fixed genus": Proposition 3, Theorem 3 (after Rémy), Corollary 3, Theorem 4; Section "Uniform generation", Proposition 4, <https://doi.org/10.48550/arXiv.1403.2908>.
