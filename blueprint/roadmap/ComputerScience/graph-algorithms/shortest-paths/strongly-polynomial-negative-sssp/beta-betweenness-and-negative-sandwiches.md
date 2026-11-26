# beta-betweenness of vertex pairs and negative sandwiches of negative vertices

Let $G$ be in split form and $\beta\in\mathbb{N}$. For vertices $u,x,v$, the *$\beta$-distance from $u$ to $v$ through $x$* is $\mathrm{thru}^\beta(u,x,v)=d^\beta(u,x)+d^\beta(x,v)$. The vertex $x$ is *$\beta$-between* $u$ and $v$ if $\mathrm{thru}^\beta(u,x,v)<0$, and the *$\beta$-betweenness* of the pair is

$$
\mathrm{BW}^\beta(u,v)=\big|\{x\in V:\mathrm{thru}^\beta(u,x,v)<0\}\big|.
$$

A *negative sandwich* is a triple $(x,U,y)$ with $x,y\in V$ and $U\subseteq N$ such that $d^1(x,u)<0$ and $d^1(u,y)<0$ for every $u\in U$; its size is $|U|$. By the distance-shift identity, $\mathrm{thru}^\beta_\phi(u,x,v)=\mathrm{thru}^\beta(u,x,v)+\phi(u)-\phi(v)$ for every price function $\phi$, independent of $\phi(x)$.

## Depends on

- [Negative vertices, h-hop distances and the negative h-hop reach](negative-vertices-and-hop-distances.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
