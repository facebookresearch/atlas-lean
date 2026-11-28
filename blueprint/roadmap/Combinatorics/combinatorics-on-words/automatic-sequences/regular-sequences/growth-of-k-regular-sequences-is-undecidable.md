# Growth problems for k-regular sequences are undecidable

No algorithm decides whether a given $k$-regular sequence is bounded, whether it lies in $\Omega(n)$, or whether it has at least polynomial growth, for sequences with real algebraic values; equality of two $k$-regular sequences, in contrast, is decidable.

Here $k\ge2$ is fixed and $\mathbb A$ is the field of real algebraic numbers. For a ring $R\subseteq\mathbb A$, a sequence is [$k$-regular over $R$](k-regular-sequences-over-a-ring.md) when the $R$-span of its $k$-kernel is finitely generated, equivalently, for $\mathbb Q\subseteq R$, when it has a linear representation $f(n)=vM_{n_0}\cdots M_{n_{s-1}}w$ with entries in $R$; for $R=\mathbb Z$ this is the [$k$-regular sequence](is-kregular-sequence.md) page. A sequence is given to an algorithm by such a linear representation, or by finitely many kernel identities with initial values; the two forms are effectively interconvertible. Growth is compared with eventual one-sided inequalities, as in Section 3 of the source: for a real sequence $g$, $f\in O(g)$ means that there are $n_0$ and $c>0$ with $f(n)\le c\,g(n)$ for all $n\ge n_0$, and $f\in\Omega(g)$ means that there are $n_0$ and $c>0$ with $f(n)\ge c\,g(n)$ for all $n\ge n_0$. A sequence is *bounded* if there is $C$ with $|f(n)|\le C$ for all $n$.

**Theorem (Krenn and Shallit).** Let $k\ge2$ be an integer.
1. It is undecidable, given a $k$-regular sequence $(f(n))_{n\ge0}$ over $\mathbb Z$ with values in $\mathbb N_0$, whether there are $n_0$ and $c>0$ with $f(n)\ge cn$ for all $n\ge n_0$.
2. For every ring $S$ with $\mathbb Q\subseteq S\subseteq\mathbb A$, it is undecidable whether a given $k$-regular sequence over $S$ is bounded.
3. For every ring $S$ with $\mathbb Q\subseteq S\subseteq\mathbb A$, it is undecidable whether a given $k$-regular sequence $(f(n))_{n\ge0}$ over $S$ has at least polynomial growth, that is, whether there is $\sigma>0$ such that for no $n_0$ and $c>0$ does $f(n)\le c\,n^\sigma$ hold for all $n\ge n_0$.

The source states clause 1 for sequences "over $S$" for every set $S$ with $\mathbb N\subseteq S\subseteq\mathbb A$, without fixing the ring of the linear representation; its reduction produces sequences that are $k$-regular over $\mathbb Z$ with values in $\mathbb N_0$, which is the case stated here.

Every $k$-regular sequence over $\mathbb A$ is $O(n^\sigma)$ for some $\sigma\ge0$, so the third problem asks whether the growth is polynomial or smaller. Boundedness is decidable for sequences with a linear representation by integer matrices (Mandel and Simon; Jacob), so clause 2 needs non-integral entries; its proof uses sequences with rational linear representations. The source also proves the analogues for $\Omega(n^\sigma(\log n)^\ell)$ and $O(n^\sigma(\log n)^\ell)$ (Corollaries C and E), under the hypotheses stated there.

## Depends on

- [$k$-regular sequence](is-kregular-sequence.md)
- [$k$-regular sequences over a ring](k-regular-sequences-over-a-ring.md)
- [Bounded sequences](../../../../Analysis/sequences-and-series/summability/permanent-summability-methods/is-bounded.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Clause 1 reduces from Hilbert's tenth problem over $\mathbb N_0$. For a polynomial $p\in\mathbb Z[x_1,\dots,x_t]$ choose $K=k^r>t+1$ and set, with $z=(n)_K$ and $|z|_d$ the number of digits $d$ in $z$,

$$
f(n)=(n+1)\,p(|z|_1,\dots,|z|_t)^2\,(|z|_{t+1}+1).
$$

This is $K$-regular over $\mathbb Z$ by Remark 1.1 of the source (digit counts are $K$-regular, and $K$-regular sequences are closed under sums and products), and hence $k$-regular by Theorem 2.9 of Allouche and Shallit, which the source cites for the passage from base $K=k^r$ to base $k$. It vanishes infinitely often if $p$ has a zero in $\mathbb N_0^t$, and otherwise $f(n)\ge n+1$; so $f\in\Omega(n)$ iff $p$ has no zero. Clause 2 reduces from the boundedness of all products of a finite set of rational matrices, and clause 3 from whether the joint spectral radius of a finite set of rational matrices is at most $1$; both are undecidable by Blondel and Tsitsiklis, and the source turns a matrix set $\{F_0,\dots,F_{k-1}\}$ into the matrix-valued sequence $F(n)=F_{n_0}\cdots F_{n_{s-1}}$ (Lemma 3.4). A good expansion links the undecidability of boundedness of rational matrix products and of the bound $\rho\le1$ on the joint spectral radius, the closure of $k$-regular sequences under sums and products, and Theorem 2.9 of Allouche and Shallit (a $k^r$-regular sequence is $k$-regular).

## Sources

- Daniel Krenn and Jeffrey Shallit, "Decidability and $k$-regular sequences", *Theoretical Computer Science* 907:34–44, 2022, doi:[10.1016/j.tcs.2022.01.018](https://doi.org/10.1016/j.tcs.2022.01.018); read in arXiv:2005.09507v3, whose numbering is used here: Theorem A (equality is decidable), Section 3 (the asymptotic notation), Theorem B, Corollary C, Theorem D with Remark 3.3, Corollary E, Theorem F with its proof and Lemma 3.4, and Section 1.4 (representations).
- Vincent D. Blondel and John N. Tsitsiklis, "The boundedness of all products of a pair of matrices is undecidable", *Systems & Control Letters* 41(2):135–140, 2000, as cited in the source above for clauses 2 and 3; not read here.
- Jean-Paul Allouche and Jeffrey Shallit, "The ring of $k$-regular sequences", *Theoretical Computer Science* 98(2):163–197, 1992, Theorem 2.9 (passage from base $k^r$ to base $k$), as cited in the first source above; not read here.
