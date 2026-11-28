# Weak pigeonhole principle is exponentially hard for Res(k)

For every constant $c>1$, refuting the $cn$ to $n$ pigeonhole principle in Res($k$) takes $2^{n^{\epsilon}}$ lines whenever $k\le\sqrt{\log n/\log\log n}$, so DNF resolution with super-constant bottom fan-in is needed for subexponential refutations of the weak pigeonhole principle.

**Res($k$).** The lines of a Res($k$) derivation are $k$-DNFs (disjunctions of conjunctions of at most $k$ literals). For $k$-DNFs $A,B$, $1\le j\le k$ and literals $l,l_1,\dots,l_j$, the rules are subsumption (from $A$ infer $A\vee l$), AND-introduction (from $A\vee l_1,\dots,A\vee l_j$ infer $A\vee\bigwedge_{i=1}^{j}l_i$), AND-elimination (from $A\vee\bigwedge_{i=1}^{j}l_i$ infer $A\vee l_i$) and cut (from $A\vee\bigwedge_{i=1}^{j}l_i$ and $B\vee\bigvee_{i=1}^{j}\neg l_i$ infer $A\vee B$). A Res($k$) refutation of a set $\mathcal C$ of $k$-DNFs is a derivation from $\mathcal C$ ending in the empty clause; its size is its number of lines, and $S_k(\mathcal C)$ is the minimum size ($\infty$ if $\mathcal C$ is satisfiable). Res($1$) is resolution.

**Pigeonhole clauses.** $\mathrm{PHP}^{m}_{n}$ has variables $x_{i,j}$ for $i\in[m]$, $j\in[n]$ and the clauses $\bigvee_{j\in[n]}x_{i,j}$ for each $i\in[m]$, and $\neg x_{i,j}\vee\neg x_{i',j}$ for all $i\ne i'$ in $[m]$ and $j\in[n]$.

**Theorem.** For every $c>1$ there is $\epsilon>0$ such that for all sufficiently large $n$, if

$$
k\le\sqrt{\frac{\log n}{\log\log n}},
$$

then every Res($k$) refutation of $\mathrm{PHP}^{cn}_{n}$ has size at least $2^{n^{\epsilon}}$.

## Expansion

The proof applies a random restriction that collapses every line of a short Res($k$) refutation to a short decision tree and then contradicts a resolution width lower bound for the restricted formula. Uniform restrictions fail here, because the hole clauses involve all $cn$ pigeons, so the argument first passes to the graph pigeonhole principle $\mathrm{PHP}(G)$ of a bipartite graph $G$ on pigeons $[cn]$ and holes $[n]$ (the clauses of $\mathrm{PHP}^{cn}_{n}$ whose variables are edges of $G$), which follows from $\mathrm{PHP}^{cn}_{n}$ by setting non-edges to $0$. A random graph gives, for some $d$, a graph with maximum degree at most $d\log n$ that is $(3/4,n/24)$-robust: under the restriction $M_{3/4}(G)$, which independently matches each hole with probability $1/4$ to a uniformly random neighbouring pigeon, the restricted formula is again a graph pigeonhole principle $\mathrm{PHP}(G-S_\rho)$ and needs resolution width at least $n/24$ with probability at least $1/2$. That width bound comes from the expansion-based width lower bound of Ben-Sasson and Wigderson.

After putting the refutation in pigeon normal form (no term asks two pigeons to share a hole; this at most doubles the size), every $i$-DNF $F$ satisfies $\Pr[F\upharpoonright_{\rho}\ne1]\le2^{-(\log e)(1-p)^i c(F)/(i\Delta^{i+1})}$, where $c(F)$ is the covering number and $\Delta$ the maximum degree. Feeding these bounds directly into the [switching lemma for small restrictions](small-restriction-switching-lemma.md), with $s_0=\frac{3}{4k}(n/24-1)$, shows that a refutation of size below $2^{n^{\epsilon}}$ has, for some $\rho$, every line of representation height at most $\sum_{i<k}s_i\le(n/24-1)/k$ while the restricted formula needs width $n/24$; converting the short decision trees into a resolution refutation of width $k$ times the height gives a contradiction. The bound on $k$ is what keeps $s_k\ge n^{\epsilon}$ after $k$ rounds of shrinking by factors of order $(d\log n)^{i+1}$.

For $k=1$ the statement is a weak pigeonhole lower bound for resolution; compare the stronger bounds for every $m>n$ in [Raz–Razborov](../../resolution-separations-and-supercritical-tradeoffs/weak-php-resolution.md). The paper notes that Atserias, Bonet and Esteban had obtained the case $k=2$, that Maciel, Pitassi and Woods give quasipolynomial-size refutations in Res($\mathrm{polylog}(n)$), and that Razborov later extended the technique to $k\le\epsilon\log n/\log\log n$.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Switching lemma for small restrictions](small-restriction-switching-lemma.md)
- [Width of a derivation](../../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Sources

- Nathan Segerlind, Samuel R. Buss, Russell Impagliazzo, "A Switching Lemma for Small Restrictions and Lower Bounds for k-DNF Resolution", *SIAM Journal on Computing*, 2004, doi:10.1137/S0097539703428555 (Definition 2.1, Definition 6.1, Theorem 6.2; proof via Definitions 6.3 to 6.8, Lemmas 6.7, 6.9 and 6.15, Theorem 6.11, Corollary 5.2; Section 1 for the related results).
