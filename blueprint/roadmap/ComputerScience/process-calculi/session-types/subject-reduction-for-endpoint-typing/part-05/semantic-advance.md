# Semantic advancement of a communicating endpoint pair

The semantic advance relation on ownership contexts has a single rule. Let $\Delta$ be an ownership
context, $e$ an endpoint, $c = (k,S)$ and $d = (k',U)$ capabilities and $S'$, $U'$ protocols such
that $\Delta(e) = c$, $\Delta(\bar e) = d$, $d \approx \bar c$ (equal ranks and $U \simeq
\overline{S}$), $c$ and $d$ have matching communication heads with continuations $S'$ and $U'$ (a
name send and a name receive, or an endpoint send and an endpoint receive with the same polarity and
rank and tree-equivalent payloads), and $U' \simeq \overline{S'}$. Then $\Delta$ advances
semantically to $\Delta[e \mapsto (k,S')][\bar e \mapsto (k',U')]$.
