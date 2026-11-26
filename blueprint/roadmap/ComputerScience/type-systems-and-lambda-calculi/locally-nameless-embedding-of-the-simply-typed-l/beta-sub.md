# Raw beta substitution at a binder depth

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$.

For $d \in \mathbb{N}$ and a raw term $a$, the raw substitution $\beta_{d,a} : \mathbb{N} \to$ raw terms sends $n$ to $\mathrm{var}\,n$ if $n < d$, to $a$ shifted by $d$ at cutoff $0$ (every variable index of $a$ increased by $d$, with the cutoff increased by one under each lambda of $a$) if $n = d$, and to $\mathrm{var}\,(n - 1)$ if $n > d$.
