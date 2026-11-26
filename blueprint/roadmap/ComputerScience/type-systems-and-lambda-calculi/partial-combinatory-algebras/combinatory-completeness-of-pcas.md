# Combinatory completeness of partial combinatory algebras

Let $A$ be a pca. For every application term $t(x, y_1, \dots, y_n)$ built from variables, constants in $A$ and application, there is a term $\lambda^* x.\, t$ in the variables $y_1, \dots, y_n$ such that for all $b, a_1, \dots, a_n \in A$: the element $(\lambda^* x.\, t)(\vec a)$ is defined, and

$$(\lambda^* x.\, t)(\vec a)\cdot b \simeq t(b, \vec a).$$

The abstraction is defined by $\lambda^* x.\,x = \mathsf{s}\,\mathsf{k}\,\mathsf{k}$, $\lambda^* x.\,u = \mathsf{k}\,u$ for $u$ a constant or a variable other than $x$, and $\lambda^* x.\,(u\,v) = \mathsf{s}\,(\lambda^* x.\,u)\,(\lambda^* x.\,v)$ for every application $u\,v$, whether or not it contains $x$. Consequently every pca has pairing, projections and a fixed-point combinator.

## Proof sketch

Induct on $t$ using the axioms: $\mathsf{s}\,\mathsf{k}\,\mathsf{k}\, b \simeq \mathsf{k}\,b\,(\mathsf{k}\,b) = b$; constants are handled by $\mathsf{k}$; and the $\mathsf{s}$ axiom distributes the argument over an application, with definedness of $\mathsf{s}\,a\,b$ guaranteeing that the abstraction itself is defined.

## Depends on

- [Partial combinatory algebra](partial-combinatory-algebra.md)

## Sources

- J. van Oosten, "Realizability: An Introduction to its Categorical Side", Studies in Logic and the Foundations of Mathematics 152, Elsevier, 2008.
- J. Longley and D. Normann, "Higher-Order Computability", Theory and Applications of Computability, Springer, 2015.
