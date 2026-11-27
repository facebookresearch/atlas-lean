# R$^0$(lin) refutes pigeonhole and Tseitin mod $p$ formulas

The $m$ to $n$ pigeonhole formulas and, for constant degree $r$ and fixed modulus $p$, the Tseitin mod $p$ formulas of $r$-regular graphs have polynomial-size R$^0$(lin) refutations.

**Pigeonhole.** $\neg\mathrm{PHP}^m_n$ consists of the pigeon axioms $(x_{i,1}=1)\vee\dots\vee(x_{i,n}=1)$ for $1\le i\le m$ and the hole axioms $(x_{i,k}=0)\vee(x_{j,k}=0)$ for $1\le i<j\le m$ and $1\le k\le n$; it is unsatisfiable when $m>n$. There is a polynomial-size [R$^0$(lin)](r0-lin-fragment.md) refutation of $\neg\mathrm{PHP}^m_n$.

**Tseitin mod $p$.** Let $p\ge2$ be a fixed integer and $G=(V,E)$ a connected undirected $r$-regular graph with $n$ vertices, no double edges and $n\equiv1\pmod p$; let $G'$ replace each edge by two opposite directed edges, and let $e[v,1],\dots,e[v,r]$ be the edges leaving $v$. The formula $\mathrm{TSE}_{G,p}$ has variables $x_{e,i}$ ($e\in E'$, $0\le i\le p-1$, "edge $e$ carries value $i$") and the translated clauses: each edge carries at least one and at most one value; $x_{e,i}$ and $x_{\bar e,p-i}$ agree for opposite edges $e,\bar e$; and for each vertex $v$ the clauses $\bigvee_{k=1}^r(x_{e[v,k],i_k}=0)$ for all $i_1,\dots,i_r\in\{0,\dots,p-1\}$ with $\sum_ki_k\not\equiv1\pmod p$, saying the values leaving $v$ sum to $1$ modulo $p$. If $r$ is a constant, $\mathrm{TSE}_{G,p}$ has polynomial-size (in $n$) R$^0$(lin) refutations.

## Expansion

Both refutations count inside R$^0$(lin). For pigeonhole, with $S$ the sum of all $x_{i,j}$, the pigeon axioms give $(S=m)\vee\dots\vee(S=mn)$ and the hole axioms give $(S=0)\vee\dots\vee(S=n)$, using that disjunctions $(z_1=a)\vee\dots$ and $(z_2=b)\vee\dots$ combine to a disjunction over $z_1+z_2$; since $m>n$ the two lines resolve to the empty disjunction. For Tseitin, summing the per-vertex sums $\alpha_v$ gives $\sum_v\alpha_v\in\{n+\ell p\}$, while pairing opposite edges shows each pair contributes $0$ or $p$, so the total is $\equiv0\pmod p$, contradicting $n\equiv1\pmod p$. Both families are hard for resolution, the pigeonhole formulas by [Haken's theorem](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md), and the same refutations transfer to [depth-3 multilinear proofs](depth-3-multilinear-proofs-simulate-r0-lin.md).

## Depends on

- [The fragment R0(lin)](r0-lin-fragment.md)

## Proof depends on

None.

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Section 6.1, Definition 6.1, Lemmas 13-14, Theorem 15; Section 6.2, Definition 6.2, Lemmas 16-18, Theorem 19).
