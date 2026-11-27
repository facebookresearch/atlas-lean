# Pointwise equal raw substitutions act equally

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$. Raw simultaneous substitution applies a map $\sigma : \mathbb{N} \to$ raw terms by $\mathrm{var}\,n \mapsto \sigma(n)$, homomorphically on applications, and $\mathrm{lam}\,A\,t \mapsto \mathrm{lam}\,A\,(t[\sigma^{\uparrow}])$, where $\sigma^{\uparrow}$ sends $0$ to $\mathrm{var}\,0$ and $n+1$ to $\sigma(n)$ renamed by the successor map.

If raw substitutions $\sigma$ and $\tau$ satisfy $\sigma(n) = \tau(n)$ for every $n \in \mathbb{N}$, then $t[\sigma] = t[\tau]$ for every raw term $t$.
