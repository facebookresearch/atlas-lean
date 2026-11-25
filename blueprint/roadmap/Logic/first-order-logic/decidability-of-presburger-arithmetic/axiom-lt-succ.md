# Presburger axiom: $x < S y$ iff $x \le y$

One of the axioms of Presburger arithmetic, in the language with $0$, $S$, $+$, $<$ and equality, is the sentence

$$\forall x\, \forall y\; \bigl(x < S y \leftrightarrow (\neg(x < y) \to x = y)\bigr),$$

where $\neg \varphi$ abbreviates $\varphi \to \bot$. The right-hand side $\neg(x < y) \to x = y$ is classically equivalent to $x < y \vee x = y$, so the axiom says $x < S y \leftrightarrow (x < y \vee x = y)$.
