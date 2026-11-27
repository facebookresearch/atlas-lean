# Function fields of characteristic greater than 2 have undecidable first-order theory

Every function field of characteristic $p > 2$, in any number of variables and over any field of constants, has an undecidable first-order theory in the language of rings without parameters; the same holds in characteristic $2$ for function fields in one variable whose constant field is algebraic over $\mathbb{F}_2$.

A *function field in $n$ variables* over a field $F$, for $n \ge 1$, is a field $K$ containing $F$ and elements $x_1, \dots, x_n$ algebraically independent over $F$ such that $K$ is a finite algebraic extension of $F(x_1, \dots, x_n)$. Its *constant field* is the algebraic closure of $F$ in $K$, a finite extension of $F$. Let $\mathcal{L}_{\mathrm{ring}} = \{+, \cdot, 0, 1\}$, with equality, and let $\operatorname{Th}(K)$ be the set of $\mathcal{L}_{\mathrm{ring}}$-sentences, without parameters from $K$, that are true in $K$.

**Theorem (Eisenträger–Shlapentokh).** Let $K$ be either

1. a function field (in any number $n \ge 1$ of variables, over any field) of characteristic $p > 2$, or
2. a function field in one variable of characteristic $2$ whose constant field is algebraic over $\mathbb{F}_2$.

Then $\operatorname{Th}(K)$ is undecidable.

The source first proves, for the same fields, that for some finite set of parameters $z_1, \dots, z_k \in K$ (depending on $K$) the theory of $K$ in $\mathcal{L}_{\mathrm{ring}} \cup \{z_1, \dots, z_k\}$ is undecidable, and then removes the parameters. The field of constants may be uncountable; undecidability means that the set of (Gödel numbers of) true parameter-free sentences is not computable.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)

## Proof depends on

- [Robinson's arithmetic Q](../../../Logic/first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md)

## Expansion

By Julia Robinson, multiplication of positive integers is first-order definable from addition and divisibility, so the theory of $(\mathbb{Z}_{>0}, +, \mid)$ is undecidable, and it suffices to build in $K$ a first-order model of $(\mathbb{Z}_{>0}, +, \mid)$. Viewing $K$ as a function field in one variable over $F(x_2, \dots, x_n)$, fix $t \in K$ with a simple zero or pole. If the set $\{(x, x^{p^s}) : x \in K,\ s \ge 0\}$, or just the powers $t^{p^s}$, is definable, the integers $s$ are represented by $t^{p^s}$ and addition and divisibility become definable relations among these elements. The source defines these $p$-th powers by generalizing earlier equations when the constant field is algebraic over a finite field, and, for higher transcendence degree of the constant field, as $x$-coordinates of rational points on a suitable elliptic curve, using a theorem of Moret-Bailly on ranks of elliptic curves that is available only in odd characteristic. This gives undecidability with finitely many parameters. To remove them, the source uses Robinson's arithmetic Q, which is finitely axiomatized and essentially undecidable (every consistent extension is undecidable): the sentences $\psi$ such that $K$ satisfies "for all parameter values $\bar w$, if the interpretation with $\bar w$ satisfies the axioms of Q then it satisfies $\psi$" form a consistent extension of Q, hence an undecidable set, and these statements are parameter-free sentences about $K$.

A good expansion adds and links pages for Robinson's definition of multiplication of positive integers from addition and divisibility, the definition of $p$-th powers in $K$ (with Moret-Bailly's theorem on ranks of elliptic curves), and the essential undecidability of Robinson's arithmetic Q.

## Sources

- Kirsten Eisenträger (Eisentraeger) and Alexandra Shlapentokh, *Undecidability in function fields of positive characteristic*, Int. Math. Res. Not. IMRN 2009, 4051–4086, https://doi.org/10.1093/imrn/rnp079. Theorem 2.1 of arXiv:0709.1739v2 is the version with parameters, Theorem 2.2 the parameter-free version stated here, proved as Corollary 5.1 of that version; the definition of a function field is in its introduction.
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5 (Section 5.2 of arXiv:1309.0441v1, for characteristic greater than $2$), which presents the result as established in its section on function fields.
