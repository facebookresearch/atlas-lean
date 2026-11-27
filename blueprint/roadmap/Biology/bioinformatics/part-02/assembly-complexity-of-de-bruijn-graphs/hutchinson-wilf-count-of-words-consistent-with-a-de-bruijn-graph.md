# Hutchinson–Wilf count of words consistent with a de Bruijn graph

Let $G = (V, E)$ be the de Bruijn multigraph of a genome on $n$ vertices ($(k-1)$-mers), with adjacency matrix $A = (a_{uv})$, where $a_{uv} \ge 0$ is the multiplicity of the edge $u \to v$ and self-loops are allowed. Write $d^+(u)$ and $d^-(u)$ for out- and in-degrees counted with multiplicity. Because $G$ arises from a single string, either $d^+(u) = d^-(u)$ for all $u$, or there is a unique start $s$ with $d^-(s) = d^+(s) - 1$ and a unique end $t$ with $d^+(t) = d^-(t) - 1$. In the balanced case choose $t$ arbitrarily. Put

$$r_u = \begin{cases} d^+(u) + 1, & u = t,\\ d^+(u), & u \ne t,\end{cases}$$

and let $L$ be the $n \times n$ matrix with diagonal entries $r_u - a_{uu}$ and off-diagonal entries $-a_{uv}$.

**Theorem.** The number of distinct words consistent with $G$ (that is, spelled by an Eulerian trail of $G$) that end at vertex $t$ is

$$\mathcal{W}(G, t) = (\det L) \left\{\prod_{u \in V} (r_u - 1)!\right\} \left\{\prod_{(u,v) \in E} a_{uv}!\right\}^{-1}.$$

For a circular, non-periodic genome, cyclic rotations ending at the $d^+(t)$ occurrences of $t$ represent one circular sequence, so the number of distinct circular genomes consistent with $G$ is $\mathcal{W}(G,t)/d^+(t)$. A genome is uniquely reconstructible from its $k$-mer multiset exactly when this count equals $1$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)
- [The (k-1)-mer walk of a string is an Eulerian trail](../../de-bruijn-graph-genome-assembly/zip-tail-kmers-perm.md)
- [Every Eulerian trail spells a string with the same k-mer multiset](../../de-bruijn-graph-genome-assembly/kmers-spell-perm.md)

## Expansion

The formula extends the BEST theorem, which counts Eulerian circuits as the number of arborescences (the determinant of a reduced Laplacian, by the matrix-tree theorem) times $\prod_u (d^+(u) - 1)!$ orderings of exits at each vertex. Two changes adapt it to words: the end vertex $t$ is visited once more than its out-degree, which is why $r_t = d^+(t)+1$; and parallel edges between the same pair of vertices spell identical letters, so permutations among the $a_{uv}$ copies of an edge give the same word and are divided out. The count is computable in polynomial time; the paper evaluates it on prokaryotic chromosomes to show that most genomes admit astronomically many reconstructions for short read lengths, driven by repeats longer than $k$.

## Sources

- C. Kingsford, M. C. Schatz and M. Pop, "Assembly complexity of prokaryotic genomes using short reads", BMC Bioinformatics 11 (2010), 21, Methods ("Counting words consistent with de Bruijn graphs"), Theorem 1 and Eq. (1), <https://doi.org/10.1186/1471-2105-11-21>, PMCID: PMC2821320.
- J. P. Hutchinson and H. S. Wilf, "On Eulerian circuits and words with prescribed adjacency patterns", Journal of Combinatorial Theory, Series A 18 (1975), 80–87, <https://doi.org/10.1016/0097-3165(75)90068-1>.
