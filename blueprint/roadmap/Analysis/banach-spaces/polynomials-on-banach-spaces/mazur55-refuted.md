# Mazur's Problem 55 has a negative answer

The [factorisation claim of Scottish Book Problem 55](scottish-book-problem55-claim.md) is false.
Pestov's continuous polynomial $W$ of degree two on $E = \ell^2$ is bounded on the open
$1$-neighbourhood of an unbounded set $R \subseteq E$ but unbounded on $\tfrac12 R$ (see
[Problem 75](mazur75-refuted.md)). It admits no factorisation $W = V \circ \varphi$ with
$\varphi : E \to F$ a continuous affine map into a normed space with $\varphi(R)$ bounded and $V$ a
continuous polynomial on $F$. Indeed $\varphi(\tfrac12 r) = \tfrac12 (\varphi(r) - \varphi(0)) + \varphi(0)$
would make $\varphi(\tfrac12 R)$ bounded too, and a continuous polynomial is bounded on bounded
sets, so $W$ would be bounded on $\tfrac12 R$.

## Sources

- S. Mazur, Problem 55 of the Scottish Book; refuted by V. Pestov, who constructs a continuous scalar-valued 2-polynomial $W$ on the separable Hilbert space $\ell^2$ and an unbounded set $R$ such that $W$ is bounded on an $\varepsilon$-neighbourhood of $R$ but does not factor through any bounded first-degree polynomial sending $R$ to a bounded set ("Two 1935 questions of Mazur about polynomials in Banach spaces: a counter-example", 1997, arXiv:funct-an/9705002). The same counterexample refutes Problem 75. In finite dimensions the answer is positive (Auerbach), so the infinite-dimensional Banach setting is essential.
