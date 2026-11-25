# Shifting de Bruijn indices

For natural numbers $d$ and $c$, shifting a term $t$ by $d$
above the cutoff $c$ adds $d$ to every variable index $i \ge c$ and leaves every index $i < c$
unchanged. The cutoff goes up by one under each binder, that is, in the body of a $\lambda$ and
in the codomain of a $\Pi$ (not in the type annotation or the domain), and sorts are unchanged.
Thus the free variables of $t$ with index at least $c$ are increased by $d$.
