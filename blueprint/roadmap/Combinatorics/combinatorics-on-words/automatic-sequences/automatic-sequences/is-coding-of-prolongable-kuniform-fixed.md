# Codings of prolongable uniform fixed points

Let $k$ be a natural number and $B$ a finite
alphabet. A sequence $w : \mathbb{N} \to B$ is a coding of a prolongable $k$-uniform fixed point
when $k \ge 2$ and there are a nonempty finite alphabet $A$, a map $f$ sending each letter of $A$
to a word of length exactly $k$ over $A$, a letter $a \in A$ with $f(a) = a\alpha$ for some
nonempty word $\alpha$ over $A$, a sequence $u : \mathbb{N} \to A$ and a map $g : A \to B$ such
that $u(0) = a$, the letter of $f(u(n))$ at position $j$ (counted from $0$) is $u(kn + j)$ for
all $n \in \mathbb{N}$ and $j < k$, and $w(n) = g(u(n))$ for all $n \in \mathbb{N}$.

The conditions on $u$ say that $u$ begins with $a$ and is fixed by $f$ applied letter by letter.

## Sources

- Sunic lines 569-584 state the equivalence and define prolongability and uniformity (`cubefree.tex`, span SHA-256 `f618b2151d7a9680b94b6865bd471b1375fb23b387579b274c1e3174b9591763`); Stipulanti lines 164-174 define morphism, coding, prolongability, and fixed point (`stip8.tex`, span SHA-256 `cbafa712ca06a7c28b1c8cd9f5d425c3b6fc518d168a321d79aed28293c2d651`).
