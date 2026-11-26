# Genome ARGs: interval-annotated inheritance graphs and their local trees

Fix a genome coordinate set $X$ (a finite set of sites $\{1,\dots,L\}$, or $[0,L)$ with intervals as annotations). A **genome ARG** (gARG) is a triple $G=(N,S,E)$ where

- $N=\{1,\dots,n\}$ is a finite set of nodes, each representing one haploid genome (the material a child inherits from one parent), and $S\subseteq N$ is the set of sample genomes;
- $E$ is a finite set of edges $(c,p,I)$ with $c,p\in N$, $c\ne p$, and $I\subseteq X$ a finite union of disjoint intervals, meaning that genome $c$ inherits the positions $I$ from the ancestral genome $p$ (possibly many generations earlier);
- the directed graph $c\to p$ is acyclic.

Call $G$ **single-parent** if for every child $c$ and position $x$ at most one edge $(c,p,I)$ has $x\in I$ (every nucleotide is inherited from exactly one parent genome or from none). Node times are optional data; only the partial order given by the graph is assumed.

**Local tree at a position.** Represent a rooted tree on $N$ by an oriented parent vector $\pi=(\pi_1,\dots,\pi_n)$ with $\pi_u\in N\cup\{0\}$ and $\pi_u=0$ for roots and for nodes absent from the tree. For a single-parent gARG and $x\in X$, the local tree $\pi^x$ is produced as follows: set $\pi_u=0$ for all $u$; for each sample $s\in S$, put $u\leftarrow s$ and repeat: find the edge $(u,p,I)$ with $x\in I$; if none exists, stop ($u$ is a root); otherwise set $\pi_u\leftarrow p$, and stop if $\pi_p\ne0$ already (the rest of the path was recorded from an earlier sample), else put $u\leftarrow p$. Acyclicity makes every trace terminate, and single-parent inheritance makes the result independent of the order of the samples.

**Arity.** The local arity of $u$ at $x$ is $a_u^x=|\{v:\pi^x_v=u\}|$ and its ARG arity is $a_u=|\{v:(v,u,I)\in E\}|$. When distinct edges have distinct child-parent pairs, $0\le a_u^x\le a_u$, because each local child $v$ of $u$ is the child of an edge into $u$. A node with $a_u^x=1$ is **locally unary** at $x$: it lies on the path of inheritance but is not a coalescence there.

**From event ARGs.** An event ARG (common-ancestor nodes with one outbound edge, recombination nodes with two outbound edges and a breakpoint $x_0$, with a fixed left/right parent convention) becomes a gARG on the same graph by annotating the outbound edge of a common-ancestor node with $[0,L)$, and the two outbound edges of a recombination node with $[0,x_0)$ and $[x_0,L)$. This annotation is in bijection with the event ARG's data; restricting each annotation to the material ancestral to $S$ (simplification) then gives a sample-resolved gARG.

## Depends on

- [Coalescence records encode a sequence of local trees exactly](tree-sequence-encoding-represents-local-trees-ex.md)
- [Coalescent with recombination: ancestral-material state space and generator](coalescent-with-recombination-ancestral-material.md)

## Expansion

Edge annotations replace event types: gene conversion, multiple crossovers and bacterial or viral recombination are all expressed by the inheritance intervals, without new node kinds. Because the ancestral material is stored on each edge, local quantities (which genomes are ancestral at $x$, local arity, coalescent span) are read off without replaying the history from the samples, which an event ARG requires. The local-tree recovery is a pastward traversal that stops at the first already-visited node, so the total work at one position is linear in the number of nodes reachable from the samples there.

## Sources

- Y. Wong, A. Ignatieva, J. Koskela et al., "A general and efficient representation of ancestral recombination graphs", Genetics (2024), iyae100, <https://doi.org/10.1093/genetics/iyae100>, PMCID PMC11373519. Sections "Genome ARGs", "Event ARGs" and "Ancestral material and sample resolution"; Appendix E ("ARGs and local trees") for the oriented-tree extraction; Appendix F ("Locally unary nodes") for local and ARG arity.
