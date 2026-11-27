# Terms of a finite type

The terms of a finite type are the formal expressions built from variables by the operation symbols; in an algebra each term defines a function of its variables.

Let $\tau$ be a finite type, as in [algebras of a finite type](algebras-of-a-finite-type.md), and let $X$ be a set of variables. The set of *terms* of type $\tau$ over $X$ is the least set of finite strings that contains every variable $x \in X$ and contains $\omega(t_1, \dots, t_n)$ whenever $\omega$ is a symbol of arity $n$ and $t_1, \dots, t_n$ are terms. In an algebra $A$ of type $\tau$, a term $t$ whose variables are among $x_1, \dots, x_m$ defines the *term function* $t^A \colon A^m \to A$, by $x_i^A(\bar a) = a_i$ and $\omega(t_1, \dots, t_n)^A(\bar a) = \omega^A(t_1^A(\bar a), \dots, t_n^A(\bar a))$.

## Depends on

- [Algebras of a finite type](algebras-of-a-finite-type.md)

## Proof depends on

None.

## Sources

- Anvar M. Nurakunov and Michał M. Stronkowski, *Profiniteness in finitely generated varieties is undecidable*, The Journal of Symbolic Logic 83 (2018), no. 4, 1566–1578, https://doi.org/10.1017/jsl.2017.89; Section 2.2 of arXiv:1712.09056v1 (terms over a set of variables, built from the basic operations).
