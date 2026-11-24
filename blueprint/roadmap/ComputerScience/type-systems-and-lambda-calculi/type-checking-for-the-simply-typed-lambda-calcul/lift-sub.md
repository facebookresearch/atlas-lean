# Lifting a raw substitution under a binder

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$.

For a raw substitution $\sigma : \mathbb{N} \to$ raw terms, its lift $\sigma^{\uparrow}$ sends $0$ to $\mathrm{var}\,0$ and $n + 1$ to the renaming of $\sigma(n)$ by the successor map $k \mapsto k + 1$, where raw renaming by a map $\rho : \mathbb{N} \to \mathbb{N}$ replaces each variable index $k$ by $\rho(k)$, lifting $\rho$ to $0 \mapsto 0$, $k+1 \mapsto \rho(k)+1$ under each lambda.
