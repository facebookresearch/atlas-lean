# Shadow Markoff mutation

A state is a pair $(x, y)$ of a classical part
$x \in \mathbb{Q}^3$ and a shadow part $y \in \mathbb{Q}^3$, with coordinates indexed by the
positions $0, 1, 2$. The shadow Markoff mutation at position $i$ replaces $x_i$ by
$x_i' = \bigl(\sum_{j \ne i} x_j^2\bigr) / x_i$ and $y_i$ by
$\bigl(-x_i' y_i + 2 \sum_{j \ne i} x_j y_j\bigr) / x_i$, and leaves every other coordinate of
$x$ and $y$ unchanged.

Division by $0$ gives $0$: if $x_i = 0$, the new $x_i$ and the new $y_i$ are both $0$.

## Sources

- Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer Sequences 27 (2024), Article 24.8.3, Section 1, equations (MutA) and (SMarmutBis).
