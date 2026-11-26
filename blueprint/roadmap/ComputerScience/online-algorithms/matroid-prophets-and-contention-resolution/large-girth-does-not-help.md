# Large girth does not improve matroid prophet ratios

For every $k$ there exists a matroid of girth at least $k$ (every circuit has at least $k$ elements) whose matroid prophet ratio is $\frac12$: for every $\varepsilon > 0$ some prophet inequality instance on it admits no online policy with ratio above $\frac12 + \varepsilon$. Hence, unlike for uniform matroids, forbidding small circuits does not allow ratios approaching $1$.

## Proof sketch

Alon, Gravin, Pollner, Rubinstein, Wang, Weinberg and Zhang construct a matroid from a high-girth hypergraph-like structure in which the gambler, after accepting any element, is blocked from most of the remaining high-value elements by long circuits, embedding the two-value worst case of the single-item prophet inequality into every circuit simultaneously.

## Depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Proof depends on

- [Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality](matroid-prophet-half.md)

## Sources

- Noga Alon, Nick Gravin, Tristan Pollner, Aviad Rubinstein, Hongao Wang, S. Matthew Weinberg, Qianfan Zhang, "A Bicriterion Concentration Inequality and Prophet Inequalities for k-Fold Matroid Unions", ITCS (2025).
