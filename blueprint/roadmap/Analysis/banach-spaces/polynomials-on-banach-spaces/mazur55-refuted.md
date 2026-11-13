# Mazur's Problem 55 has a negative answer

The factorisation claim of Scottish Book
Problem 55 is false: there are a real Banach space $E$, an unbounded set $R \subseteq E$ and a
continuous bilinear form $B : E \times E \to \mathbb{R}$ such that for some $\varepsilon > 0$
the quadratic form $W(x) = B(x, x)$ is bounded on the set of points at distance less than
$\varepsilon$ from $R$, yet there are no continuous linear functional $L : E \to \mathbb{R}$,
constant $c \in \mathbb{R}$ and real polynomial $V$ with $W(x) = V(L(x) + c)$ for all $x \in E$
and $|L(r) + c|$ bounded for $r \in R$.

## Sources

- S. Mazur, Problem 55 of the Scottish Book; refuted by V. Pestov, who constructs a continuous scalar-valued 2-polynomial `W` on the separable Hilbert space `ℓ²` and an unbounded set `R` such that `W` is bounded on an `ε`-neighbourhood of `R` but does not factor through any bounded first-degree polynomial sending `R` to a bounded set ("Two 1935 questions of Mazur about polynomials in Banach spaces: a counter-example", 1997, arXiv:funct-an/9705002). The same counterexample refutes Problem 75. In finite dimensions the answer is positive (Auerbach), so the infinite-dimensional Banach setting is essential.
