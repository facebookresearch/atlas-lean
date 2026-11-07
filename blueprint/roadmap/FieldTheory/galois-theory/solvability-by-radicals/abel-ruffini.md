# Abel–Ruffini theorem

Let $n \ge 1$ be a natural number. Every complex root of every
polynomial with rational coefficients of degree exactly $n$ is expressible by radicals over
$\mathbb{Q}$ if and only if $n \le 4$. Here a complex number is expressible by radicals over
$\mathbb{Q}$ when it lies in the smallest subfield $S$ of $\mathbb{C}$ such that $z \in S$
whenever $z \in \mathbb{C}$ and $z^k \in S$ for some integer $k \ge 1$.

The direction from radical solvability to $n \le 4$ is the classical insolvability of the
general quintic, extended to higher degrees; the converse follows from the explicit formulas
of Cardano and Ferrari for degrees at most four.

## Sources

- P. Ruffini (1799), N. H. Abel (1824), É. Galois (1832). Listed as §57 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf); the general-quintic insolvability is #16 on Freek Wiedijk's *Formalizing 100 Theorems* list (https://www.cs.ru.nl/~freek/100/). Taken verbatim, with no Lean variant, from leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e, manifest `manifests/problems/abel_ruffini.toml` (statement revision 1), module `LeanEval.Algebra.AbelRuffini`, hole `abel_ruffini`.
