# Kleene's second model on Baire space is a partial combinatory algebra

Let $\mathcal{B} = \mathbb{N}^{\mathbb{N}}$ be Baire space. For $a, x \in \mathcal{B}$ read $a$ as an oracle program with a parameter: $a(0)$ indexes an oracle Turing functional and the tail $a' = (a(n+1))_n$ is a parameter oracle. Define $a \cdot x$ to be the function $n \mapsto \Phi_{a(0)}^{a' \oplus x}(n)$ when this is total, and undefined otherwise, where $a' \oplus x$ is the join of the two oracles. Then $(\mathcal{B}, \cdot)$ is a partial combinatory algebra, *Kleene's second model* $\mathcal{K}_2$. Its application represents exactly the continuous partial functions on Baire space with $G_\delta$ domains, coded by elements of $\mathcal{B}$.

## Proof sketch

The combinators are built from oracle-uniform s-m-n and universal oracle functionals: the parameter tail allows an element to carry previously supplied arguments, so currying is implemented by prepending data to the parameter oracle.

## Depends on

- [Partial combinatory algebra](partial-combinatory-algebra.md)

## Proof depends on

- [A pca from an s-m-n theorem and a universal function](pca-from-smn-and-universal-function.md)

## Sources

- S. C. Kleene and R. E. Vesley, "The Foundations of Intuitionistic Mathematics, Especially in Relation to Recursive Functions", North-Holland, 1965.
- J. van Oosten, "Realizability: An Introduction to its Categorical Side", Studies in Logic and the Foundations of Mathematics 152, Elsevier, 2008.
- J. Longley and D. Normann, "Higher-Order Computability", Theory and Applications of Computability, Springer, 2015.
