# Moving a capability across a union preserves the union

Let $\Delta$, $\Theta$ be ownership contexts, $d$ an endpoint and $c$ a capability with $\Delta(d) =
c$. Then $(\Delta \setminus d) \cup \Theta[d \mapsto c] = \Delta \cup \Theta$, where in a union the
entry of the left context is taken when both contexts contain a key.
