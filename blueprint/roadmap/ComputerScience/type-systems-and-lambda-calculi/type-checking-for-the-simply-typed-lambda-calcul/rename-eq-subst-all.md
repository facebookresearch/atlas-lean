# Raw renaming is substitution by variables

Raw terms over a type $B$ of base types are de Bruijn variables $\mathrm{var}\,n$ ($n \in \mathbb{N}$), applications $\mathrm{app}\,f\,a$, and abstractions $\mathrm{lam}\,A\,t$ annotated with a simple type $A$. Raw simultaneous substitution applies a map $\sigma : \mathbb{N} \to$ raw terms by $\mathrm{var}\,n \mapsto \sigma(n)$, homomorphically on applications, and $\mathrm{lam}\,A\,t \mapsto \mathrm{lam}\,A\,(t[\sigma^{\uparrow}])$, where $\sigma^{\uparrow}$ sends $0$ to $\mathrm{var}\,0$ and $n+1$ to $\sigma(n)$ renamed by the successor map.

For every map $\rho : \mathbb{N} \to \mathbb{N}$ and raw term $t$, the renaming of $t$ by $\rho$ equals $t[\sigma]$ for the substitution $\sigma(n) = \mathrm{var}\,\rho(n)$, where raw renaming by a map $\rho : \mathbb{N} \to \mathbb{N}$ replaces each variable index $k$ by $\rho(k)$, lifting $\rho$ to $0 \mapsto 0$, $k+1 \mapsto \rho(k)+1$ under each lambda.
