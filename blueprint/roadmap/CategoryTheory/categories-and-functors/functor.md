# Functor

Let $\mathsf{C}$ and $\mathsf{D}$ be categories. A *functor* $F\colon \mathsf{C} \to \mathsf{D}$ assigns to each object $X$ of $\mathsf{C}$ an object $F(X)$ of $\mathsf{D}$, and to each morphism $f\colon X \to Y$ of $\mathsf{C}$ a morphism $F(f)\colon F(X) \to F(Y)$ of $\mathsf{D}$, such that $F(1_X) = 1_{F(X)}$ for every object $X$ and $F(g \circ f) = F(g) \circ F(f)$ for all morphisms $f\colon X \to Y$ and $g\colon Y \to Z$.

## Sources

- Emily Riehl, Category Theory in Context, Dover Publications, 2016.
