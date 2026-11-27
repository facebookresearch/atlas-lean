# Polynomial with rational critical values

Let $\overline{\mathbb{Q}}$ be an algebraic closure of $\mathbb{Q}$ and $S \subset
\overline{\mathbb{Q}}$ a finite set. Then there is a nonconstant polynomial $p \in
\mathbb{Q}[z]$ such that $p(s) \in \mathbb{Q}$ for every $s \in S$ and $p(r) \in \mathbb{Q}$ for
every $r \in \overline{\mathbb{Q}}$ with $p'(r) = 0$.

Köck states the lemma as: $p(S)$ and the critical values of $p \colon \mathbb{P}^1 \to
\mathbb{P}^1$ lie in $\mathbb{Q} \cup \{\infty\}$. The critical values of a nonconstant polynomial
other than $\infty$ are among the values $p(r)$ at the zeros $r$ of $p'$
([branch points of a polynomial map](branch-points-of-a-polynomial-map.md)), so the form above
gives his.

## Depends on

None among the pages.

## Proof depends on

None among the pages.

## Proof sketch

The proof is Köck's induction on the number $n$ of elements of $S$, which may be assumed closed
under conjugation. If $n \le 1$, then $S \subset \mathbb{Q}$ and $p = z$ works. Otherwise the
product $p_1$ of the distinct minimal polynomials of the elements of $S$ has degree $n$ and vanishes on $S$;
the set $S_1 = \{p_1(r) : p_1'(r) = 0\}$ has at most $n - 1$ elements and is closed under
conjugation, so by induction there is $p_2$ for $S_1$. Then $p = p_2 \circ p_1$ works: $p(S) =
\{p_2(0)\} \subset \mathbb{Q}$, and if $p'(r) = p_2'(p_1(r)) \, p_1'(r) = 0$, then either
$p_1(r) \in S_1$ or $p_1(r)$ is a zero of $p_2'$, and in both cases $p(r) = p_2(p_1(r)) \in
\mathbb{Q}$.

## Sources

- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, Lemma 3.5 and its proof, pp. 262–263.
