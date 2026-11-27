# Depth Tour Aux eq

For every tree $t$, depth $d$ and list $\mathit{acc}$ of vertex-depth pairs, the accumulator form of the depth-annotated Euler tour returns the depth-annotated tour followed by the accumulator: $\mathrm{depthTourAux}(t, d, \mathit{acc}) = \mathrm{depthTour}(d, t) \mathbin{+\!\!+} \mathit{acc}$. For example, for a leaf labelled $x$ at depth $0$ and $\mathit{acc} = [(y, 0)]$ the result is $[(x, 0), (y, 0)]$.
