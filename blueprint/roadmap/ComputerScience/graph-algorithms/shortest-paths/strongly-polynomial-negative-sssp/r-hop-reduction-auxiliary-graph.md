# r-hop reductions and the layered hop-reducing auxiliary graph

Let $G=(V,E^{+}\cup N,w)$ have $w\ge 0$ on $E^{+}$, and let $r\ge 1$. A weighted graph $H=(V_H,E_H,w_H)$ with $V\subseteq V_H$ is an *$r$-hop reduction* of $G$ if for all $h\ge 0$ and $u,v\in V$

$$
\mathrm{dist}^h_G(u,v)\ge\mathrm{dist}^{\lceil h/r\rceil}_H(u,v)\ge\mathrm{dist}_G(u,v),
$$

so that every $h$-hop walk of $G$ is simulated by a $\lceil h/r\rceil$-hop walk of $H$. The *layered construction* takes copies $v_0=v,v_1,\dots,v_r$ of every vertex, the edge $(u_i,v_i)$ for each $(u,v)\in E^{+}$ and $0\le i\le r$, the edge $(u_i,v_{i+1})$ for each $(u,v)\in N$ and $0\le i<r$, and return edges $(v_i,v_0)$; with $\delta_i(v)=\mathrm{dist}^i_G(V,v)$ it sets $w_H(u_i,v_j)=w(u,v)+\delta_i(u)-\delta_j(v)$ (in particular $w_H(v_i,v_0)=\delta_i(v)\le 0$, since $\delta_0\equiv 0$), so that only return edges can be negative and these serve as the hops of $H$. It has $O(rm)$ edges and its weights are computable in $\tilde O(rm)$ time.

## Depends on

- [Negative vertices, h-hop distances and the negative h-hop reach](negative-vertices-and-hop-distances.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
