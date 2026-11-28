# The induction axiom of Presburger arithmetic

Let $k \in \mathbb{N}$ and let $\varphi(x, y_1, \dots, y_k)$ be a formula of the language of Presburger arithmetic ($0$, $S$, $+$, $<$, $=$) with one bound variable $x$ (the induction variable) and free variables among the parameters $y_1, \dots, y_k$. The induction axiom for $\varphi$ is the sentence

$$\forall y_1 \cdots \forall y_k\; \Bigl[\varphi(0, \vec y) \to \Bigl(\forall x\, \bigl(\varphi(x, \vec y) \to \varphi(S x, \vec y)\bigr) \to \forall x\, \varphi(x, \vec y)\Bigr)\Bigr],$$

obtained by universally closing over the parameters. This is the induction schema with parameters.

## Sources

- H. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001, §3.7, p. 269, which gives the universal closures of the induction formulas as axioms of Peano arithmetic; the schema here is the same schema restricted to formulas of the Presburger language.
