# Decoding inverts encoding

Let $E$ be a finite set with $m$ elements, listed in a fixed
order as $e_0, \dots, e_{m-1}$. Encode a subset $T \subseteq E$ as the point $x_T$ of the Boolean
cube of dimension $m$ whose $j$-th coordinate is false exactly when $e_j \in T$, and decode a
point $x$ as the subset $\{e_j : x_j = \mathrm{false}\}$. Then for every subset $T \subseteq E$,
decoding $x_T$ gives back $T$.
