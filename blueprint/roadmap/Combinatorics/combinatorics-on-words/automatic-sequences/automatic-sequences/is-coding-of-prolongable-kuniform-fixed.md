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

- Zoran Šunić, *Rational Tree Morphisms and Transducer Integer Sequences: Definition and Examples*, Journal of Integer Sequences 10 (2007), Article 07.4.3, Section 3, discussion after Definition 3.1 (Cobham's theorem, prolongable and $k$-uniform endomorphisms), https://cs.uwaterloo.ca/journals/JIS/VOL10/Sunic/cubefree.html
- Narad Rampersad and Manon Stipulanti, *The Formal Inverse of the Period-Doubling Sequence*, Journal of Integer Sequences 21 (2018), Article 18.9.1, Section 2.1 (morphisms, codings, prolongability and fixed points), https://cs.uwaterloo.ca/journals/JIS/VOL21/Stipulanti/stip8.html
