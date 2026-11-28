# Res(k+1) is exponentially stronger than Res(k)

For every constant $k\ge1$ there are unsatisfiable CNFs, variants of graph ordering principles on sparse graphs, with polynomial-size Res($k+1$) refutations that need exponential size in Res($k$); one family even has constant-width clauses. So the Res($k$) hierarchy is strict, exponentially, at every level.

Res($k$) is the refutation system whose lines are $k$-DNFs, with subsumption, AND-introduction and AND-elimination of at most $k$ literals and the cut rule from $A\vee\bigwedge_{i=1}^{j}l_i$ and $B\vee\bigvee_{i=1}^{j}\neg l_i$ to $A\vee B$ ($j\le k$); size counts lines, and Res($1$) is resolution.

**Graph ordering principles.** Let $G$ be an undirected graph with neighbourhoods $N(u)$, and take a variable $X_{u,v}$ for each ordered pair of distinct vertices. $\mathrm{GOP}(G)$ consists of the clauses
$\neg X_{u,v}\vee\neg X_{v,w}\vee X_{u,w}$ (transitivity), $\neg X_{u,v}\vee\neg X_{v,u}$ for $u\ne v$ (antisymmetry), and $\bigvee_{v\in N(u)}X_{v,u}$ for every vertex $u$ (no locally minimal element). $\mathrm{GOP}^{k}(G)$ replaces each $X_{u,v}$ by a conjunction $X^1_{u,v}\wedge\dots\wedge X^k_{u,v}$ of $k$ new variables and expands to clauses by distributivity and De Morgan. $\mathrm{GOP}^{\oplus k}(G)$ instead replaces each literal $X_{u,v}$ by the $k$-DNF $\mathrm{Odd}(X^1_{u,v},\dots,X^k_{u,v})$ and each literal $\neg X_{u,v}$ by $\mathrm{Even}(X^1_{u,v},\dots,X^k_{u,v})$, then expands to clauses.

**Theorem.** Let $k\ge1$ be an integer.

1. There are constants $c>0$ and $\epsilon_k>0$ and, for all sufficiently large $n$, graphs $G$ on $n$ vertices of maximum degree at most $c\log n$ such that every Res($k$) refutation of $\mathrm{GOP}^{k+1}(G)$ has size $2^{\Omega(n^{\epsilon_k})}$. For every graph with $n$ vertices and maximum degree at most $d\ge3$, $\mathrm{GOP}^{k}(G)$ has a Res($k$) refutation of size $O(n^3k^d)$; with $k+1$ in place of $k$ and $d=c\log n$ this is $n^{O(1)}$.
2. There are constants $d>0$ and $\epsilon_k>0$ and, for all sufficiently large $n$, graphs $G$ on $n$ vertices of maximum degree at most $d$ such that every Res($k$) refutation of $\mathrm{GOP}^{\oplus(k+1)}(G)$ has size $2^{\Omega(\epsilon_k n)}$. For each $k$ and every graph with $n$ vertices and maximum degree at most $d\ge3$, $\mathrm{GOP}^{\oplus k}(G)$ has at most $2^{O(dk)}n^3$ clauses, each of width at most $dk$, and a Res($k$) refutation of size $2^{O(dk)}n^3$.

## Expansion

*Upper bounds.* $\mathrm{GOP}(G)$ has a resolution refutation of size $O(n^3)$, a variant of the standard refutation of the ordering principle that successively derives that each element has a predecessor among the larger-indexed ones. Substituting the conjunctions (or the parity DNFs) for the variables turns it into a Res($k$) derivation over the substituted formulas; the clauses of $\mathrm{GOP}^{k}(G)$ yield those $k$-DNFs by $O(k^d)$ AND-introductions each. In the parity version each resolution step on $X_{u,v}$ becomes a constant-size Res($k$) derivation, because Res($k$) refutes the pair $\mathrm{Even}(X_1,\dots,X_k)$, $\mathrm{Odd}(X_1,\dots,X_k)$ in some constant number of lines depending only on $k$.

*Lower bounds.* Each proof uses a restriction distribution $P_{k+1}(G)$ under which a term of at most $k$ literals is satisfied with probability bounded below while the restricted formula still needs large resolution width. In part 1, $\rho$ colours the vertices randomly with $4k$ colours and, for each pair $u,v$ of distinct colours, sets the block $X^1_{u,v},\dots,X^{k+1}_{u,v}$ to a uniformly random assignment with at least one $0$, so the conjunction is false and $\mathrm{GOP}^{k+1}(G)\upharpoonright_\rho=\mathrm{GOP}^{k+1}(G\setminus B_\rho)$, where $B_\rho$ is the set of bichromatic edges. In part 2 one uniformly chosen variable of each block stays free and the others are set at random, so the parity of the block remains undetermined. Then every $k$-DNF $F$ satisfies $\Pr[F\upharpoonright_\rho\ne1]\le d\,2^{-\delta c(F)^{\gamma}}$ (in part 2 with $\gamma=1$), and the normal form of the [switching lemma for small restrictions](small-restriction-switching-lemma.md) collapses all lines of a short Res($k$) refutation to decision trees of height at most $(n/96k-1)/k$ in part 1 and $(n/12-1)/k$ in part 2. The decision-tree-to-resolution conversion then gives a refutation of the restricted formula of width at most $n/96k-1$, respectively $n/12-1$, contradicting width lower bounds for graph ordering principles: in part 1 the graph is an $(n/96k)$-robust random graph of degree $\Theta(\log n)$, whose monochromatic part keeps large connected neighborly components, and in part 2 it is a connected $\tfrac16$-neighborly random graph of constant degree ($\epsilon$-neighborly means every two disjoint vertex sets of size at least $\epsilon n$ are joined by an edge).

The paper calls this the first Res($k+1$) versus Res($k$) separation for $k\ge2$; for $k=1$ it improves the earlier $2^{\Omega(2^{\log^{\epsilon}n})}$ separation of Res($2$) from resolution by Atserias and Bonet to $2^{\Omega(n^{\epsilon})}$. The first family uses clauses of width $\Theta(\log n)$; the parity family brings the width down to a constant.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Switching lemma for small restrictions](small-restriction-switching-lemma.md)
- [Width of a derivation](../../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Sources

- Nathan Segerlind, Samuel R. Buss, Russell Impagliazzo, "A Switching Lemma for Small Restrictions and Lower Bounds for k-DNF Resolution", *SIAM Journal on Computing*, 2004, doi:10.1137/S0097539703428555 (Definition 2.1; part 1: Definition 8.1, Theorem 8.2 restated as Theorem 8.23, Lemmas 8.3 and 8.4; part 2: Definition 9.1, Theorem 9.2 restated as Theorem 9.9, Lemmas 9.4 and 9.5; lower-bound proofs via Definitions 8.5 and 9.6, Corollaries 3.4 and 5.2; Section 1 for the comparison with earlier separations).
