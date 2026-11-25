# Proper Cycle Comparison

Proper direct image of nearby and vanishing cycles. Let $X$, $Y$ be complex varieties with
regular functions $s$ on $X$ and $t$ on $Y$, closed subvarieties `A`, `B` presenting their zero
loci, and a proper morphism $g : X \to Y$ with $t \circ g = s$ that restricts to $g_0$ between
the zero loci (`FunctionMorphism`). For the given derived direct-image data on this diagram
(`DiagramDerivedData`), functorial K-injective resolutions `R₁`, `R₂` on the exponential covers
and their compatibilities `E₁`, `E₂` with the deck translation, this constructs an isomorphism,
natural in bounded constructible complexes $K$ of sheaves of $\mathbb{Q}$-vector spaces on
$X(\mathbb{C})$, from the nearby/vanishing cycle triangle of $Rg_* K$ to $Rg_{0*}$ of the cycle
triangle of $K$. Its first component is the base-change map for restriction to the zero loci and
its second component is the canonical comparison `properNearbyComparison`; its third
(vanishing-cycle) component is only required to complete these to an isomorphism of triangles,
and the isomorphism intertwines the nearby and the vanishing monodromies.
