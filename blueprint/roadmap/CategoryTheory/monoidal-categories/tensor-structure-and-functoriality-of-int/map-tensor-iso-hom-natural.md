# Naturality of the tensor comparison of an Int lift

Let $C$ and $D$ be symmetric monoidal categories with symmetric traces $T$ and $S$, and let $\mathrm{Int}(T)$ be the [Int construction](../the-int-construction/README.md), whose objects are pairs $X = (X^+, X^-)$ and whose morphisms $X \to Y$ are crossed morphisms $X^+ \otimes Y^- \to Y^+ \otimes X^-$. For a braided strong monoidal $F : C \to D$ preserving $T$ relative to $S$, with [induced functor](../the-int-construction/map.md) $L(F)$ and its [tensor comparison](map-tensor-iso.md) $\mu^L$, for all Int morphisms $f : X_1 \to Y_1$ and $g : X_2 \to Y_2$,

$$(L(F)f \otimes L(F)g) ; \mu^L_{Y_1,Y_2} = \mu^L_{X_1,X_2} ; L(F)(f \otimes g).$$
