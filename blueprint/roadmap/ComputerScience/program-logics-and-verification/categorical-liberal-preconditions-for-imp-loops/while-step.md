# Guarded liberal while transformer

For an IMP guard $b$, body $c$ and postcondition $Q$, define the monotone transformer on sets of states by $F(I)=\{s:(b(s)=\mathrm{false}\Rightarrow Q(s))\land(b(s)=\mathrm{true}\Rightarrow\operatorname{wlp}(c,\mathbf1_I)(s))\}$. Here $\mathbf1_I$ denotes the membership predicate, not a numeric indicator.
