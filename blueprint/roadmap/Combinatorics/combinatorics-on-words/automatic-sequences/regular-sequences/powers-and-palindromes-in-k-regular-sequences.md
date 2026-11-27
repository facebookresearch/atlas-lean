# Whether a k-regular sequence contains an α-power or a palindrome is undecidable

For every integer $\alpha\ge2$, no algorithm decides whether a given $k$-regular sequence contains an $\alpha$-power, for example a square, and none decides whether it contains a nontrivial palindrome; for automatic sequences both questions are decidable.

Here $k\ge2$ is fixed, $\mathbb A$ is the set of real algebraic numbers, and a sequence $(f(n))_{n\ge0}$ *over* $S$ is a $k$-regular sequence in the sense of Allouche and Shallit with values in $S$: its $k$-kernel $\{(f(k^en+i))_{n\ge0} : e\ge0,\ 0\le i<k^e\}$ spans a finitely generated module, equivalently $f(n)=vM_{n_0}\cdots M_{n_{s-1}}w$ for a row vector $v$, a column vector $w$ and square matrices $M_0,\dots,M_{k-1}$, where $n_{s-1}\cdots n_0$ is the base-$k$ expansion of $n$. A sequence is given to an algorithm by such a linear representation, or by finitely many kernel identities with initial values; the two forms are effectively interconvertible. For an integer $\alpha\ge2$, an *$\alpha$-power* in $(f(n))_{n\ge0}$ is a nonempty block $f(i),f(i+1),\dots,f(i+\alpha m-1)$ with $m\ge1$ and $f(i+t)=f(i+sm+t)$ for all $0\le s<\alpha$ and $0\le t<m$; a $2$-power is a *square*. A *palindrome* is a nonempty block that reads the same forwards and backwards, and it is *nontrivial* if its length is at least $2$.

**Theorem (Krenn and Shallit).** Let $k\ge2$ and $\alpha\ge2$ be integers.
1. It is undecidable whether a given $k$-regular sequence contains an $\alpha$-power.
2. It is undecidable whether a given $k$-regular sequence contains a nontrivial palindrome.

For $k$-automatic sequences, which take finitely many values, the existence of squares, higher powers and nontrivial palindromes is decidable.

## Depends on

- [$k$-regular sequence](is-kregular-sequence.md)
- [$k$-automatic sequence (finite-kernel definition)](../automatic-sequences/is-kautomatic.md)

## Proof depends on

None.

## Expansion

Both clauses reduce from whether a $k$-regular sequence has a zero term, which is undecidable by Theorem 5.2 of Allouche and Shallit. Given $f$, the sequence $g$ with $g(0)=1$ and

$$
g(n)=g(n-1)+f(n-\alpha+1)^2\cdots f(n-2)^2f(n-1)^2\qquad(n\ge1),
$$

with the convention $f(-i)=1$ for $i\ge1$, is effectively $k$-regular and nondecreasing; it contains an $\alpha$-power iff $\alpha$ consecutive terms are equal, which happens iff $f$ has a zero term. For squares $g(n)=1+f(0)^2+\cdots+f(n-1)^2$. The same sequence works for nontrivial palindromes. A good expansion links the undecidability of the zero-term problem for $k$-regular sequences and the closure of $k$-regular sequences under products, shifts and partial sums used to build $g$, which have no pages.

## Sources

- Daniel Krenn and Jeffrey Shallit, "Decidability and $k$-regular sequences", *Theoretical Computer Science* 907:34–44, 2022, doi:[10.1016/j.tcs.2022.01.018](https://doi.org/10.1016/j.tcs.2022.01.018); read in arXiv:2005.09507v3, whose numbering is used here: Section 5 (the definitions of $\alpha$-powers and palindromes), Theorems M and N and the proof of Theorem M.
- Jean-Paul Allouche and Jeffrey Shallit, "The ring of $k$-regular sequences", *Theoretical Computer Science* 98(2):163–197, 1992, Theorem 5.2 (zero terms), as cited in the source above; not read here.
