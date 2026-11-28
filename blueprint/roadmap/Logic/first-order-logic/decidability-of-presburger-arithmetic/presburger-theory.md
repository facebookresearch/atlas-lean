# The axioms of Presburger arithmetic

Presburger arithmetic is the theory in the language with $0$, $S$, $+$, $<$ and equality whose axioms are the sentences ($\neg \varphi$ abbreviates $\varphi \to \bot$)

1. $\forall x\; \neg(S x = 0)$;
2. $\forall x\, \forall y\; (S x = S y \to x = y)$;
3. $\forall x\; (x + 0 = x)$;
4. $\forall x\, \forall y\; (x + S y = S(x + y))$;
5. $\forall x\; \neg(x < 0)$;
6. $\forall x\, \forall y\; \bigl(x < S y \leftrightarrow (\neg(x < y) \to x = y)\bigr)$;
7. $\forall x\, \forall y\; \bigl(\neg(x < y) \to (\neg(x = y) \to y < x)\bigr)$;

together with, for every $k \in \mathbb{N}$ and every formula $\varphi(x, y_1, \dots, y_k)$ with one bound variable $x$ and parameters $y_1, \dots, y_k$, the induction axiom

$$\forall \vec y\; \Bigl[\varphi(0, \vec y) \to \Bigl(\forall x\, \bigl(\varphi(x, \vec y) \to \varphi(S x, \vec y)\bigr) \to \forall x\, \varphi(x, \vec y)\Bigr)\Bigr].$$
