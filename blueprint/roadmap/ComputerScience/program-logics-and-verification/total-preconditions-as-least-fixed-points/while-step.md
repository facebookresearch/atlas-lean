# Guarded total-correctness transformer

For an IMP guard $b$, body $c$ and assertion $Q$, define the monotone transformer $F(I)=\{s:(b(s)=\mathrm{false}\land Q(s))\lor(b(s)=\mathrm{true}\land\operatorname{wp}(c,\mathbf1_I)(s))\}$. The body precondition requires termination in $I$; $\mathbf1_I$ denotes the membership predicate.
