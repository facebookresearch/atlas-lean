# Terms of a first-order language

The terms of a first-order language over a set of variables are the formal expressions built from the variables by applying function symbols; a nullary function symbol is a term by itself.

Let $L$ be a first-order language, with a set of $n$-ary function symbols for each $n \ge 0$, and let $\alpha$ be a set of variables. The set of *terms* of $L$ over $\alpha$ is the least set that contains a term $x$ for every variable $x \in \alpha$ and contains $f(t_1, \dots, t_n)$ whenever $f$ is an $n$-ary function symbol and $t_1, \dots, t_n$ are terms; for $n = 0$ this is the term $f$.

For a finite type $\tau$, as in [algebras of a finite type](algebras-of-a-finite-type.md), take the language whose $n$-ary function symbols are the symbols of $\tau$ of arity $n$ and which has no relation symbols. Its terms over a set $X$ of variables are the terms of type $\tau$ over $X$ of universal algebra, nullary symbols included.

## Sources

- Stanley Burris and H. P. Sankappanavar, *A Course in Universal Algebra*, Graduate Texts in Mathematics 78, Springer, 1981, https://doi.org/10.1007/978-1-4613-8130-3; read in the authors' Millennium Edition (2012 update), https://www.math.uwaterloo.ca/~snburris/htdocs/UALG/univ-algebra2012.pdf, Chapter II, Definition 10.1 (terms of a type over a set of variables).
