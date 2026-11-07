# A Catalan generating function for two sets of five patterns

Let
$B = \{010, 101, 102, 201, 210\}$ and $B' = \{011, 101, 110, 201, 210\}$, where a pattern is
written as a digit string ($101$ is the triple $(1, 0, 1)$). For a set $A$ of patterns let
$F_A(x) = \sum_{n \ge 1} |I_n(A)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $A$, and let $C(x) = \sum_{n \ge 0} C_n x^n$ be the
generating function of the Catalan numbers $C_n = \binom{2n}{n}/(n + 1)$. Then $F_B = F_{B'}$
and

$$(1 - x)(2 - C(x)) F_B(x) = x.$$

Since $C(x) = (1 - \sqrt{1 - 4x})/(2x)$ and $(1 - x)(2 - C(x))$ is a unit in $\mathbb{Q}[[x]]$,
this says $F_B(x) = F_{B'}(x) = x / ((1 - x)(2 - (1 - \sqrt{1 - 4x})/(2x)))$.

## Sources

- Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024), Article A76, Theorem 3 (`integers-2024-A76-thm-3`).
