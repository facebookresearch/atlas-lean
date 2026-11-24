# Raw beta substitution at depth zero is single-variable substitution

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$. For $d \in \mathbb{N}$ and a raw term $a$, $\beta_{d,a}$ sends $n < d$ to $\mathrm{var}\,n$, $d$ to $a$ shifted by $d$ at cutoff $0$, and $n > d$ to $\mathrm{var}\,(n-1)$.

For every raw term $a$, $\beta_{0,a}$ equals the single-variable raw substitution for $a$, which sends $0$ to $a$ and $n + 1$ to $\mathrm{var}\,n$.
