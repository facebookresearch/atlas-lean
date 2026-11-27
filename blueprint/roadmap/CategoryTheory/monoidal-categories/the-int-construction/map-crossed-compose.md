# The crossed action of a trace-preserving functor respects Int composition

Let $C$ and $D$ be symmetric monoidal categories with symmetric traces $T$ and $S$, and let $\mathrm{Int}(T)$ be the [Int construction](README.md), whose objects are pairs $X = (X^+, X^-)$ and whose morphisms $X \to Y$ are crossed morphisms $X^+ \otimes Y^- \to Y^+ \otimes X^-$. For a braided strong monoidal functor $F : C \to D$, with tensor comparison $\mu$ and its inverse $\delta$, write $F^\times(f) = \mu_{A,V} ; F(f) ; \delta_{B,U}$ for its action on a crossed arrow $f : A \otimes V \to B \otimes U$, where $;$ is composition in forward order. If $F$ preserves $T$ relative to $S$ (the braided structure also makes $F$ preserve the symmetry, which Int composition uses), then for crossed arrows $f : A \otimes V \to B \otimes U$ and $g : B \otimes W \to E \otimes V$,

$$F^\times(\mathrm{compose}_T(f, g)) = \mathrm{compose}_S(F^\times(f), F^\times(g)).$$
