# Rows of the generalized hyperbolic Pascal triangle

Fix $q \in \mathbb{N}$, a type $R$ with
an addition, and leg sequences $\alpha, \beta \colon \mathbb{N} \to R$ (left and right). Row $n$ of
the generalized hyperbolic Pascal triangle linked to the mosaic $\{4, q\}$ is the list of its
vertices from left to right, each recorded as a pair (type code, value) as in the interior step,
with code $0$ for the wingers. Row $1$ is $(0, \alpha_1), (0, \beta_1)$, and for $n \ge 1$ row
$n + 1$ is $(0, \alpha_{n+1})$, followed by the interior step applied to row $n$, followed by
$(0, \beta_{n+1})$. Row $0$ (the indeterminate root $\Omega$) is represented by the empty list.

## Sources

- Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Section 1 (construction of the triangle linked to `{4, q}`, Figure 1).
