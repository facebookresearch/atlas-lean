# Kleene's first model is a partial combinatory algebra

Let $\varphi_0, \varphi_1, \dots$ be an acceptable numbering of the partial recursive functions $\mathbb{N} \rightharpoonup \mathbb{N}$. Define the partial application $e \cdot n \simeq \varphi_e(n)$ on $\mathbb{N}$. Then $(\mathbb{N}, \cdot)$ is a partial combinatory algebra, called *Kleene's first model* $\mathcal{K}_1$. More generally, for every total function $f : \mathbb{N} \to \mathbb{N}$, application $e \cdot n \simeq \varphi^f_e(n)$ by the $e$-th partial function recursive in $f$ gives a pca $\mathcal{K}_1^f$.

## Proof sketch

The s-m-n theorem and the universal partial recursive function (in their oracle-uniform forms for the relativized model) provide the hypotheses of the s-m-n construction of a pca.

## Depends on

- [Partial combinatory algebra](partial-combinatory-algebra.md)
- [Parametrized s-m-n theorem](../../../TheoryOfComputation/computability/exists-computable-code.md)

## Proof depends on

- [A pca from an s-m-n theorem and a universal function](pca-from-smn-and-universal-function.md)

## Sources

- S. C. Kleene, "Introduction to Metamathematics", North-Holland and Van Nostrand, 1952.
- J. van Oosten, "Realizability: An Introduction to its Categorical Side", Studies in Logic and the Foundations of Mathematics 152, Elsevier, 2008.
- J. Longley and D. Normann, "Higher-Order Computability", Theory and Applications of Computability, Springer, 2015.
