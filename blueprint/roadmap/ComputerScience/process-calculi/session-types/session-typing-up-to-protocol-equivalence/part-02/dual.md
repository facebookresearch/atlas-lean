# Head matching transfers to dual protocols

Let $\mathcal{R}$, $\mathcal{S}$ be binary relations on protocols and $S$, $T$ protocols related by
the head match $\mathcal{H}(\mathcal{R})$ (same head constructor and metadata, $\mathcal{R}$-related
payloads and continuations). Suppose $\mathcal{R} \subseteq \mathcal{S}$ and that $A
\mathrel{\mathcal{R}} B$ implies $\overline{A} \mathrel{\mathcal{S}} \overline{B}$. Then
$\overline{S}$ and $\overline{T}$ are related by $\mathcal{H}(\mathcal{S})$. (Duality exchanges
sends and receives and dualizes continuations, but leaves payloads unchanged.)
