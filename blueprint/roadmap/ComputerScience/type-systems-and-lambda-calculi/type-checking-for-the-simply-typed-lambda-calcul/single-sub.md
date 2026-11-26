# Single-variable raw substitution

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$.

For a raw term $a$, the single-variable raw substitution sends $0$ to $a$ and $n + 1$ to $\mathrm{var}\,n$ for every $n \in \mathbb{N}$.
