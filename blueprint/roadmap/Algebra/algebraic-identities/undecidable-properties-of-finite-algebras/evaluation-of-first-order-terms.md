# Evaluation of terms in a structure

Given values for its variables, a term of a first-order language takes a value in a structure for that language: a variable takes its assigned value, and a function symbol applied to terms takes the symbol's interpretation at their values.

Let $L$ be a first-order language and $M$ an $L$-structure, in which each $n$-ary function symbol $f$ is interpreted by a map $f^M \colon M^n \to M$. Let $v \colon \alpha \to M$ assign an element to each variable. The *value* $t^M[v] \in M$ of a [term](terms-of-a-first-order-language.md) $t$ of $L$ over $\alpha$ is defined by recursion on $t$: $x^M[v] = v(x)$ for a variable $x$, and $f(t_1, \dots, t_n)^M[v] = f^M(t_1^M[v], \dots, t_n^M[v])$.

For an [algebra](algebras-of-a-finite-type.md) $A$ of a finite type, read as a structure for the language of that type, and variables $x_1, \dots, x_m$, the map $\bar a \mapsto t^A[x_i \mapsto a_i]$ is the *term function* $t^A \colon A^m \to A$ of universal algebra.

## Sources

- Stanley Burris and H. P. Sankappanavar, *A Course in Universal Algebra*, Graduate Texts in Mathematics 78, Springer, 1981, https://doi.org/10.1007/978-1-4613-8130-3; read in the authors' Millennium Edition (2012 update), https://www.math.uwaterloo.ca/~snburris/htdocs/UALG/univ-algebra2012.pdf, Chapter II, Definition 10.2 (the term function of a term in an algebra).
