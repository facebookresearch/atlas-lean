# Composition Data

Composition data for derived pullback along morphisms of schemes $f : X \to Y$ and
$g : Y \to Z$, for the derived pullbacks given by `HasDerivedPullbacks`: a natural isomorphism
$Lf^* \circ Lg^* \cong L(g \circ f)^*$ such that, at every cochain complex $P$ of
$\mathcal{O}_Z$-modules, its component followed by the counit $L(g \circ f)^* P \to (g \circ f)^* P$
equals $Lf^*$ of the counit $Lg^* P \to g^* P$, then the counit $Lf^* (g^* P) \to f^* g^* P$, then
the termwise composition isomorphism $f^* g^* P \cong (g \circ f)^* P$ (`compositionComplexIso`).
