# k-regular sequences over a ring

A sequence with entries in a commutative ring $R$ is $k$-regular over $R$ when the $R$-module spanned by its $k$-kernel is finitely generated; over a field this means the span is finite-dimensional, equivalently the sequence has a linear representation by matrices over $R$.

Let $k\ge2$ be an integer and let $R$ be a [commutative ring with identity](../../../../Algebra/rings-and-fields/commutative-ring-with-identity.md). The sequences $(f(n))_{n\ge0}$ with $f(n)\in R$ form an $R$-module under termwise addition and scalar multiplication. The *$k$-kernel* of $f$ is the set of sequences

$$
\{(f(k^en+i))_{n\ge0} : e\ge0,\ 0\le i<k^e\},
$$

and $f$ is *$k$-regular over $R$* if the $R$-submodule spanned by its $k$-kernel is [finitely generated](../../../../RingTheory/modules/finitely-generated-module.md). For $R=\mathbb Z$ this is the notion of the [$k$-regular sequence](is-kregular-sequence.md) page. When $R$ is a field, which is the case for every ring $R$ with $\mathbb Q\subseteq R\subseteq\mathbb A$, where $\mathbb A$ is the field of real algebraic numbers, $f$ is $k$-regular over $R$ exactly when that span is a finite-dimensional vector space, and exactly when $f$ has a *linear representation over $R$*: a row vector $v$, a column vector $w$ and square matrices $M_0,\dots,M_{k-1}$, all with entries in $R$ and of matching sizes, such that

$$
f(n)=vM_{n_0}\cdots M_{n_{s-1}}w\qquad\text{for all }n\ge0,
$$

where $n_{s-1}\cdots n_0$ is the base-$k$ expansion of $n$ (empty for $n=0$, the empty product being the identity matrix).

## Depends on

- [Commutative ring with identity](../../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Finitely generated module](../../../../RingTheory/modules/finitely-generated-module.md)

## Proof depends on

None.

## Expansion

Over a field, the equivalence with linear representations goes as follows. If the span of the $k$-kernel has a basis $g_1,\dots,g_r$ of kernel sequences, each sequence $(g_j(kn+d))_{n\ge0}$ with $0\le d<k$ lies in the span again, which defines the matrices $M_d$; conversely, for $n\ge1$, $f(k^en+i)=vM_{i_0}\cdots M_{i_{e-1}}M_{n_0}\cdots M_{n_{s-1}}w$, where $i_{e-1}\cdots i_0$ is $i$ written with $e$ digits, so the entries of the column vectors $M_{n_0}\cdots M_{n_{s-1}}w$, together with the sequence that is $1$ at $n=0$ and $0$ elsewhere, span a finite-dimensional space containing the $k$-kernel. A good expansion links this equivalence, Theorem 2.2 of Allouche and Shallit as recalled by Krenn and Shallit.

## Sources

- Daniel Krenn and Jeffrey Shallit, "Decidability and $k$-regular sequences", *Theoretical Computer Science* 907:34–44, 2022, doi:[10.1016/j.tcs.2022.01.018](https://doi.org/10.1016/j.tcs.2022.01.018); read in arXiv:2005.09507v3, whose numbering is used here: Section 1 (the $k$-kernel and the definition of $k$-regular sequences by a finitely generated module) and Section 1.4 (linear representations, citing Theorem 2.2 of Allouche and Shallit).
- Jean-Paul Allouche and Jeffrey Shallit, "The ring of $k$-regular sequences", *Theoretical Computer Science* 98(2):163–197, 1992, Theorem 2.2 (linear representations), as cited in the source above; not read here.
