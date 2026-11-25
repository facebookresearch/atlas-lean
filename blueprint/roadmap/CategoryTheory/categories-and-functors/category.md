# Category

A *category* consists of:

- a collection of *objects*;
- for any two objects $X$ and $Y$, a collection $\operatorname{Hom}(X, Y)$ of *morphisms* $f\colon X \to Y$;
- for each object $X$, an *identity morphism* $1_X\colon X \to X$;
- for any two morphisms $f\colon X \to Y$ and $g\colon Y \to Z$, a *composite* $g \circ f\colon X \to Z$.

These satisfy the unit laws $f \circ 1_X = f$ and $1_Y \circ f = f$ for every morphism $f\colon X \to Y$, and associativity $h \circ (g \circ f) = (h \circ g) \circ f$ for all morphisms $f\colon W \to X$, $g\colon X \to Y$ and $h\colon Y \to Z$.

## Sources

- Emily Riehl, Category Theory in Context, Dover Publications, 2016.
