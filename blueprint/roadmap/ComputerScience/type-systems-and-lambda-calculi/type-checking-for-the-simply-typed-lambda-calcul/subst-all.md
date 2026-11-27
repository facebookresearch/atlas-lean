# Simultaneous substitution on raw terms

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$.

For a raw substitution $\sigma : \mathbb{N} \to$ raw terms, $t[\sigma]$ is defined by recursion on $t$: $(\mathrm{var}\,n)[\sigma] = \sigma(n)$, $(\mathrm{app}\,f\,a)[\sigma] = \mathrm{app}\,(f[\sigma])\,(a[\sigma])$, and $(\mathrm{lam}\,A\,t)[\sigma] = \mathrm{lam}\,A\,(t[\sigma^{\uparrow}])$, where $\sigma^{\uparrow}$ sends $0$ to $\mathrm{var}\,0$ and $n + 1$ to $\sigma(n)$ with every variable index $k$ renamed to $k + 1$ (the renaming lifted under binders).
