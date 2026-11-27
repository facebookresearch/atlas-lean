# Associativity of the Int composite comparison

Let $C$, $D$, $E$, $B$ be symmetric monoidal categories with symmetric traces $T$, $S$, $R$, $Q$, and let $\mathrm{Int}(T)$ be the [Int construction](../the-int-construction/README.md), whose objects are pairs $X = (X^+, X^-)$ and whose morphisms $X \to Y$ are crossed morphisms $X^+ \otimes Y^- \to Y^+ \otimes X^-$. For composable braided strong monoidal functors preserving the traces, write $L$ for the [induced Int functors](../the-int-construction/map.md), $K(F, G) : L(F ; G) \cong L(F) ; L(G)$ for the [composite comparison](map-comp-iso.md), $e : L(\mathrm{id}) \cong \mathrm{id}$ for the [identity comparison](map-id-iso.md), $\star$ for whiskering, and $L(\cdot)$ also for the [lift of a monoidal natural isomorphism](map-iso.md). For $F : C \to D$, $G : D \to E$, $H : E \to B$,

$$K(F;G, H) ; (K(F, G) \star LH) ; \alpha_{LF, LG, LH} = L(\alpha_{F,G,H}) ; K(F, G;H) ; (LF \star K(G, H)),$$

where the $\alpha$ on the left is the associator of the lifts and $L(\alpha_{F,G,H})$ is the lift of the input functors' associator.
