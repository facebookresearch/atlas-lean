# Image and preimage problems for k-regular sequences are undecidable

No algorithm decides whether a given $k$-regular sequence takes every natural number (or every integer) as a value, whether two such sequences have the same image, whether some value is taken twice, or whether the base-$k$ expansions of a preimage form a regular language.

Here $k\ge2$ is fixed, $\mathbb A$ is the set of real algebraic numbers, and a sequence $(f(n))_{n\ge0}$ *over* $S$ is a $k$-regular sequence in the sense of Allouche and Shallit with values in $S$: its $k$-kernel $\{(f(k^en+i))_{n\ge0} : e\ge0,\ 0\le i<k^e\}$ spans a finitely generated module, equivalently $f(n)=vM_{n_0}\cdots M_{n_{s-1}}w$ for a row vector $v$, a column vector $w$ and square matrices $M_0,\dots,M_{k-1}$, where $n_{s-1}\cdots n_0$ is the base-$k$ expansion of $n$. A sequence is given to an algorithm by such a linear representation, or by finitely many kernel identities with initial values; the two forms are effectively interconvertible. For a value $q$, the *language associated with* $f^{-1}(q)$ is $\{(n)_k : f(n)=q\}$, where $(n)_k$ is the base-$k$ expansion of $n$ with no leading zeros.

**Theorem (Krenn and Shallit).** Let $k\ge2$ be an integer.
1. For every set $S\supseteq\mathbb N_0$, it is undecidable, given a $k$-regular sequence $f$ over $S$ and $q\in S$, whether the language associated with $f^{-1}(q)$ is regular, that is, recognized by a deterministic finite automaton.
2. For every set $S\supseteq\mathbb N_0$, it is undecidable whether a given $k$-regular sequence $f$ over $S$ satisfies $\{f(n):n\in\mathbb N_0\}=\mathbb N_0$.
3. For every set $S\supseteq\mathbb Z$, it is undecidable whether a given $k$-regular sequence $f$ over $S$ satisfies $\{f(n):n\in\mathbb N_0\}=\mathbb Z$.
4. For every set $S\supseteq\mathbb N_0$, it is undecidable whether two given $k$-regular sequences over $S$ have the same image.
5. For every set $S\supseteq\mathbb N_0$, it is undecidable whether a given $k$-regular sequence over $S$ takes some value twice.

Whether a $k$-regular sequence has a zero term is undecidable as well (Allouche and Shallit, Theorem 5.2 of *The ring of $k$-regular sequences*), while equality of two $k$-regular sequences is decidable.

## Depends on

- [$k$-regular sequence](is-kregular-sequence.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Regular languages are closed under left quotients by fixed words](../../../../TheoryOfComputation/regular-languages/syntactic-monoids/language-quotients-and-syntactic-monoids/left-quotient-2.md)

## Expansion

Clauses 1, 2, 3 and 5 reduce from Hilbert's tenth problem over $\mathbb N_0$, using that $n\mapsto p(|z|_1,\dots,|z|_t)$ with $z=(n)_K$, $K=k^r>t$, is $k$-regular for every integer polynomial $p$. For clause 2, the sequence equal to $n/2+1$ at even $n$ and to $p(|z|_1,\dots,|z|_t)^2$ at odd $n$ covers $\mathbb N$, and its image is $\mathbb N_0$ iff $p$ has a zero; clause 3 uses three residue classes modulo $3$ in the same way. Clause 4 follows from clause 2 by comparing with $g(n)=n$. For clause 5, a sequence $f$ with $f(n+1)-f(n)=g(n)\ge0$ built from $g=p(\dots)^2$ is strictly increasing iff $p$ has no zero. For clause 1, $f(n)=p(|z|_1,\dots,|z|_t)^2+(|z|_{t+1}-|z|_{t+2})^2$ with $K>t+2$ has empty zero set if $p$ has no zero, and otherwise its zero language would yield, by intersection with a regular language and a left quotient by a fixed word, the nonregular language $\{(t+1)^{m-1}(t+2)^m : m\ge1\}$. Hilbert's tenth problem enters through the Davis–Putnam–Robinson–Matiyasevich theorem. A good expansion links the $k$-regularity of $n\mapsto p(|z|_1,\dots,|z|_t)$ and the closure of $k$-regular sequences under sums and products, the closure of regular languages under intersection, and the nonregularity of $\{(t+1)^{m-1}(t+2)^m : m\ge1\}$, which have no pages.

## Sources

- Daniel Krenn and Jeffrey Shallit, "Decidability and $k$-regular sequences", *Theoretical Computer Science* 907:34–44, 2022, doi:[10.1016/j.tcs.2022.01.018](https://doi.org/10.1016/j.tcs.2022.01.018); read in arXiv:2005.09507v3, whose numbering is used here: Theorem H (with the remark on Theorem 5.3 of Allouche and Shallit), Theorems I and J, Corollary K, and Theorem L with their proofs, Remark 1.1, and the remark before Section 4.1 on zero terms.
- Jean-Paul Allouche and Jeffrey Shallit, "The ring of $k$-regular sequences", *Theoretical Computer Science* 98(2):163–197, 1992, Theorem 5.2 (zero terms), as cited in the source above; not read here.
