# Hilbert's tenth problem is undecidable over the rational function field in two variables over the complex numbers

There is no algorithm that decides, for a polynomial equation with coefficients in $\mathbb{Z}[t_1, t_2]$, whether it has a solution in the field $\mathbb{C}(t_1, t_2)$ of rational functions in two variables over $\mathbb{C}$.

Let $K = \mathbb{C}(t_1, t_2)$, the field of rational functions in two independent variables $t_1, t_2$ over $\mathbb{C}$.

**Theorem (Kim–Roush).** Hilbert's tenth problem for $K$ with coefficients in $\mathbb{Z}[t_1, t_2]$ is undecidable: there is no algorithm that decides, for a polynomial $f \in \mathbb{Z}[t_1, t_2][x_1, \dots, x_n]$, whether $f$ has a zero in $K^n$.

Conventions: $K$ is uncountable, so the coefficients are restricted to the finitely generated ring $\mathbb{Z}[t_1, t_2]$.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Following Denef's method, the proof builds a Diophantine model in $K$, with coefficients in $\mathbb{Z}[t_1, t_2]$, of the structure $\langle \mathbb{Z} \times \mathbb{Z}, +, \mid, \mathcal{Z}, \mathcal{W} \rangle$, where $+$ is componentwise addition, $(n, 1) \mid (m, s)$ holds exactly when $m = ns$, $\mathcal{Z}(n, m)$ holds exactly when $m = 0$, and $\mathcal{W}((m, n), (r, s))$ holds exactly when $m = s$ and $n = r$; the existential theory of this structure is undecidable because multiplication of integers can be recovered from it. The pairs of integers are represented by pairs of points on two quadratic twists of a fixed elliptic curve $E : y^2 = x^3 + ax + b$ over $\mathbb{Q}$ without complex multiplication, namely $(t_i^3 + a t_i + b) Y^2 = X^3 + aX + b$ for $i = 1, 2$; each has rank one over $K$, generated modulo torsion by the point $(t_i, 1)$, and the pair $(m, n)$ corresponds to the multiples $m(t_1, 1)$ and $n(t_2, 1)$. The relations are then expressed through the coordinates of these points. A good expansion links pages for the rank-one twists of $E$ over $K$, for the existential undecidability of the structure $\langle \mathbb{Z} \times \mathbb{Z}, +, \mid, \mathcal{Z}, \mathcal{W} \rangle$, and for the transfer of undecidability along a Diophantine model.

## Sources

- K. H. Kim and F. W. Roush, *Diophantine undecidability of $\mathbb{C}(t_1, t_2)$*, J. Algebra 150 (1992), no. 1, 35–44, https://doi.org/10.1016/S0021-8693(05)80047-X; the statement as recalled in Theorem 4.1 of the version of the second source read.
- Kirsten Eisenträger (Eisentraeger), *Hilbert's tenth problem for function fields of characteristic zero*, in: Model Theory with Applications to Algebra and Analysis, Cambridge University Press, 2008, pp. 237–254, https://doi.org/10.1017/CBO9780511735219.008; Theorem 4.1 of arXiv:math/0610162v1 states the result and its section on $\mathbb{C}(t_1, t_2)$ outlines the proof.
