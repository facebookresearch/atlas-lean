# Uniform random function on n + 1 points splits into head and tail

Let $X$ be a finite nonempty type and $n \in \mathbb{N}$. The uniform distribution on functions $\mathrm{Fin}(n+1) \to X$ equals the distribution obtained by drawing $x$ uniformly from $X$, then independently drawing $g$ uniformly from functions $\mathrm{Fin}\,n \to X$, and returning $\mathrm{cons}(x, g)$, the function sending $0$ to $x$ and $i + 1$ to $g(i)$.
