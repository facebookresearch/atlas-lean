# Right unit law for the Int composite comparison

Let $C$, $D$, $E$, $B$ be symmetric monoidal categories with symmetric traces $T$, $S$, $R$, $Q$, and let $\mathrm{Int}(T)$ be the [Int construction](../the-int-construction/README.md), whose objects are pairs $X = (X^+, X^-)$ and whose morphisms $X \to Y$ are crossed morphisms $X^+ \otimes Y^- \to Y^+ \otimes X^-$. For composable braided strong monoidal functors preserving the traces, write $L$ for the [induced Int functors](../the-int-construction/map.md), $K(F, G) : L(F ; G) \cong L(F) ; L(G)$ for the [composite comparison](map-comp-iso.md), $e : L(\mathrm{id}) \cong \mathrm{id}$ for the [identity comparison](map-id-iso.md), $\star$ for whiskering, and $L(\cdot)$ also for the [lift of a monoidal natural isomorphism](map-iso.md). For $F : C \to D$,

$$K(F, \mathrm{id}) ; (LF \star e) ; \rho_{LF} = L(\rho_F),$$

comparing the right unitor of the lift with the lift of the input functor's right unitor.
