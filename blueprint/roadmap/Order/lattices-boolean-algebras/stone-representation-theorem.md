# Stone representation theorem

Every Boolean algebra $B$ embeds in a power set algebra: there
are a set $X$ and an injective map $f$ from $B$ to the power set of $X$ such that
$f(a \sqcup b) = f(a) \cup f(b)$ and $f(a \sqcap b) = f(a) \cap f(b)$ for all $a, b \in B$,
$f(\top) = X$ and $f(\bot) = \emptyset$.

Such a map automatically preserves complements: $f(a^c) = X \setminus f(a)$ for all $a \in B$.

## Sources

- M. H. Stone, The Theory of Representation for Boolean Algebras, Trans. Amer. Math. Soc. 40 (1936), 37–111, DOI 10.2307/1989664.
