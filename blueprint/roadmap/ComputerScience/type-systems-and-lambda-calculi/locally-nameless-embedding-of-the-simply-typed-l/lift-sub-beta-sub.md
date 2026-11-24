# Lifting a raw beta substitution increments its depth

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$. For $d \in \mathbb{N}$ and a raw term $a$, $\beta_{d,a}$ sends $n < d$ to $\mathrm{var}\,n$, $d$ to $a$ shifted by $d$ at cutoff $0$, and $n > d$ to $\mathrm{var}\,(n-1)$. The lift $\sigma^{\uparrow}$ of a raw substitution sends $0$ to $\mathrm{var}\,0$ and $n + 1$ to $\sigma(n)$ with every variable index $k$ renamed to $k + 1$ (the renaming lifted under binders).

For every $d \in \mathbb{N}$ and raw term $a$, $(\beta_{d,a})^{\uparrow} = \beta_{d+1,a}$ as functions on $\mathbb{N}$.
