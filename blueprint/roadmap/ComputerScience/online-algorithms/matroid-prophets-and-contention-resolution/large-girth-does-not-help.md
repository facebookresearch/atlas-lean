# Large girth does not improve matroid prophet ratios

For every $k$ there exist a matroid of girth at least $k$ (every circuit has at least $k$ elements) and a prophet inequality instance on it whose optimal competitive ratio is exactly $\frac12$. Hence, unlike for uniform matroids, forbidding small circuits does not allow ratios approaching $1$.

## Proof sketch

Alon, Gravin, Pollner, Rubinstein, Wang, Weinberg and Zhang construct a matroid from a high-girth hypergraph-like structure in which the gambler, after accepting any element, is blocked from most of the remaining high-value elements by long circuits, embedding the two-value worst case of the single-item prophet inequality into every circuit simultaneously.

## Depends on

- [Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality](matroid-prophet-half.md)

## Proof depends on

- [Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality](matroid-prophet-half.md)

## Sources

- Noga Alon, Nick Gravin, Tristan Pollner, Aviad Rubinstein, Hongao Wang, S. Matthew Weinberg, Qianfan Zhang, "A Bicriterion Concentration Inequality and Prophet Inequalities for k-Fold Matroid Unions", ITCS (2025).
