# Partial combinatory algebra

A *partial combinatory algebra* (pca) is a set $A$ with a partial binary operation $(a, b) \mapsto a \cdot b$ (application, associating to the left) and two elements $\mathsf{k}, \mathsf{s} \in A$ such that for all $a, b, c \in A$:

1. $\mathsf{k}\cdot a \cdot b$ is defined and equals $a$;
2. $\mathsf{s}\cdot a\cdot b$ is defined; and
3. $\mathsf{s}\cdot a\cdot b\cdot c \simeq (a\cdot c)\cdot(b\cdot c)$,

where $\simeq$ is Kleene equality: one side is defined iff the other is, and then they are equal. An application expression is defined only if all its subexpressions are defined.

## Sources

- J. van Oosten, "Realizability: An Introduction to its Categorical Side", Studies in Logic and the Foundations of Mathematics 152, Elsevier, 2008.
- J. Longley and D. Normann, "Higher-Order Computability", Theory and Applications of Computability, Springer, 2015.
