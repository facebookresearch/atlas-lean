# Induction axiom

For a formula $\varphi(x, \vec y)$ of the language of arithmetic with one induction variable $x$ and $k$
parameters $\vec y = (y_1, \dots, y_k)$, the induction axiom is the sentence
$$\forall \vec y \, \Bigl[\varphi(0, \vec y) \to \bigl(\forall x \, (\varphi(x, \vec y) \to \varphi(S x, \vec y))\bigr) \to \forall x \, \varphi(x, \vec y)\Bigr].$$
The body is built with the parameters free, substituting for and quantifying the induction variable,
and the parameters are then universally closed. For $k = 0$ this is the parameter-free induction axiom.

## Sources

- H. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001, Section 3.4.
