# Preservation of symmetric traces by a monoidal functor

Let $C$ and $D$ be symmetric monoidal categories with [symmetric traces](symmetric-trace.md) $T$ and $S$, and $F : C \to D$ a strong monoidal functor with tensor comparisons $\mu_{X,U} : FX \otimes FU \to F(X \otimes U)$ and their inverses $\delta_{X,U}$. Then $F$ preserves the traces when, for every $f : X \otimes U \to Y \otimes U$,

$$F\bigl(\operatorname{Tr}_T^U(f)\bigr) = \operatorname{Tr}_S^{FU}\bigl(\delta_{Y,U} \circ F(f) \circ \mu_{X,U}\bigr).$$

The trace on the right is taken of the comparison-adjusted morphism $FX \otimes FU \to FY \otimes FU$, not of $F(f) : F(X \otimes U) \to F(Y \otimes U)$.
