# Monoidal functors preserve traces along exact pairings

Let $C$ and $D$ be symmetric monoidal categories and $F : C \to D$ a braided strong monoidal functor, with tensor comparisons $\mu_{X,U} : FX \otimes FU \to F(X \otimes U)$ and their inverses $\delta_{X,U}$. If $V$ is a right dual of $U$ through an exact pairing, then $FV$ is a right dual of $FU$ through the image pairing, and for every $f : X \otimes U \to Y \otimes U$ the [traces along these pairings](trace-of-pairing.md) satisfy

$$F\bigl(\operatorname{tr}_V(f)\bigr) = \operatorname{tr}_{FV}\bigl(\delta_{Y,U} \circ F(f) \circ \mu_{X,U}\bigr).$$
