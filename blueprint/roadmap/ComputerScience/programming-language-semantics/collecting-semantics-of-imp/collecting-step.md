# Collecting transformer of IMP

For sets $I$ and $X$ of IMP configurations, the collecting transformer with initial set $I$ maps $X$ to

$$F_I(X) = I \cup \{d \mid \exists c \in X,\ c \to d\},$$

where $\to$ is the [small-step relation](../operational-semantics-of-imp/step.md) of IMP. It keeps the initial configurations and adds the one-step successors of the configurations in $X$, not those of $I$: for $X = \emptyset$ the result is $I$.
