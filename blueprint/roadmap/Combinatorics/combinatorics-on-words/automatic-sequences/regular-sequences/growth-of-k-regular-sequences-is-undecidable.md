# Growth problems for k-regular sequences are undecidable

No algorithm decides whether a given $k$-regular sequence is bounded, whether it lies in $\Omega(n)$, or whether it has at least polynomial growth, for sequences with real algebraic values; equality of two $k$-regular sequences, in contrast, is decidable.

Here $k\ge2$ is fixed, $\mathbb A$ is the set of real algebraic numbers, and a sequence $(f(n))_{n\ge0}$ *over* $S$ is a $k$-regular sequence in the sense of Allouche and Shallit with values in $S$: its $k$-kernel $\{(f(k^en+i))_{n\ge0} : e\ge0,\ 0\le i<k^e\}$ spans a finitely generated module, equivalently $f(n)=vM_{n_0}\cdots M_{n_{s-1}}w$ for a row vector $v$, a column vector $w$ and square matrices $M_0,\dots,M_{k-1}$, where $n_{s-1}\cdots n_0$ is the base-$k$ expansion of $n$. A sequence is given to an algorithm by such a linear representation, or by finitely many kernel identities with initial values; the two forms are effectively interconvertible.

**Theorem (Krenn and Shallit).** Let $k\ge2$ be an integer.
1. For every set $S$ with $\mathbb N\subseteq S\subseteq\mathbb A$, it is undecidable whether a given $k$-regular sequence $(f(n))_{n\ge0}$ over $S$ is in $\Omega(n)$.
2. For every ring $S$ with $\mathbb Q\subseteq S\subseteq\mathbb A$, it is undecidable whether a given $k$-regular sequence over $S$ is bounded.
3. For every ring $S$ with $\mathbb Q\subseteq S\subseteq\mathbb A$, it is undecidable whether a given $k$-regular sequence $(f(n))_{n\ge0}$ over $S$ has at least polynomial growth, that is, whether there is $\sigma>0$ with $f(n)\notin O(n^\sigma)$.

Every $k$-regular sequence over $\mathbb A$ is $O(n^\sigma)$ for some $\sigma\ge0$, so the third problem asks whether the growth is polynomial or smaller. Boundedness is decidable for sequences with a linear representation by integer matrices (Mandel and Simon; Jacob), so clause 2 needs non-integral entries. The source also proves the analogues for $\Omega(n^\sigma(\log n)^\ell)$ and $O(n^\sigma(\log n)^\ell)$ (Corollaries C and E), under the hypotheses stated there.

## Depends on

- [$k$-regular sequence](is-kregular-sequence.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Clause 1 reduces from Hilbert's tenth problem over $\mathbb N_0$. For a polynomial $p\in\mathbb Z[x_1,\dots,x_t]$ choose $K=k^r>t+1$ and set, with $z=(n)_K$ and $|z|_d$ the number of digits $d$ in $z$,

$$
f(n)=(n+1)\,p(|z|_1,\dots,|z|_t)^2\,(|z|_{t+1}+1).
$$

This is $K$-regular, hence $k$-regular, by the closure of $k$-regular sequences under sums and products. It vanishes infinitely often if $p$ has a zero in $\mathbb N_0^t$, and otherwise $f(n)\ge n+1$; so $f\in\Omega(n)$ iff $p$ has no zero. Clause 2 reduces from the boundedness of all products of a finite set of rational matrices, and clause 3 from whether the joint spectral radius of a finite set of rational matrices is at most $1$; both are undecidable by Blondel and Tsitsiklis, and the source turns a matrix set $\{F_0,\dots,F_{k-1}\}$ into the matrix-valued sequence $F(n)=F_{n_0}\cdots F_{n_{s-1}}$ (Lemma 3.4). A good expansion links the undecidability of boundedness of rational matrix products and of the bound $\rho\le1$ on the joint spectral radius, and the closure of $k$-regular sequences under sums and products, which have no pages.

## Sources

- Daniel Krenn and Jeffrey Shallit, "Decidability and $k$-regular sequences", *Theoretical Computer Science* 907:34–44, 2022, doi:[10.1016/j.tcs.2022.01.018](https://doi.org/10.1016/j.tcs.2022.01.018); read in arXiv:2005.09507v3, whose numbering is used here: Theorem A (equality is decidable), Theorem B, Corollary C, Theorem D with Remark 3.3, Corollary E, Theorem F with its proof and Lemma 3.4, and Section 1.4 (representations).
- Vincent D. Blondel and John N. Tsitsiklis, "The boundedness of all products of a pair of matrices is undecidable", *Systems & Control Letters* 41(2):135–140, 2000, as cited in the source above for clauses 2 and 3; not read here.
