# Mazur's Scottish Book Problem 75 fails in general Banach spaces

The [Scottish Book Problem 75 claim](scottish-book-problem75-claim.md) is false: there are a real
Banach space $E$ (one can take $E = \ell^2$), an unbounded set $R \subseteq E$, a continuous
polynomial $W : E \to \mathbb{R}$ of degree two that is not homogeneous, and $\alpha = \tfrac12$
such that $|W|$ is bounded on the open $1$-neighbourhood of $R$ but unbounded on $\alpha R$, hence
on every open $\delta$-neighbourhood of $\alpha R$ (Pestov). On $\ell^\infty$, Pestov takes
$R = \{n e_n : n \in \mathbb{N}\}$ and the coordinatewise polynomial
$W(x)_n = x_n (x_n - n)/(n + 1)$, then composes with the inclusion $\ell^2 \to \ell^\infty$ and a
bounded linear functional to obtain a scalar polynomial on $\ell^2$.

No homogeneous quadratic $W(x) = B(x, x)$ can be a counterexample, since $W(\alpha x) = \alpha^2 W(x)$.

## Sources

- S. Mazur, Problem 75 of the Scottish Book; refuted by V. Pestov, whose counterexample to Problem 55 is a continuous scalar-valued 2-polynomial $W$ on $\ell^2$, bounded on an $\varepsilon$-neighbourhood of an unbounded set $R$, but unbounded on $\tfrac12 R$, hence unbounded on every neighbourhood of $\tfrac12 R$ ("Two 1935 questions of Mazur about polynomials in Banach spaces: a counter-example", 1997, arXiv:funct-an/9705002). Plichko and Zagorodnyuk gave an independent negative solution ("On automatic continuity and three problems of 'The Scottish Book' concerning the boundedness of polynomial functionals", J. Math. Anal. Appl. 220 (1998), 477–494). In the Euclidean case the statement is true, per typescript Ad 75.
