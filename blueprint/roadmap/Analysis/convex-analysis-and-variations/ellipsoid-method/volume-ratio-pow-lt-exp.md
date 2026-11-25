# Volume after $k$ central-cut steps

For $n \ge 2$ and $k \ge 1$, $\rho_n^{\,k} < e^{-k/(2(n+1))}$, so after $k$ steps $\mathrm{vol}\, E_k < e^{-k/(2(n+1))}\, \mathrm{vol}\, E_0$. If $P$ has positive volume and $E_0 \supseteq P$, the method therefore [finds a point of $P$](ellipsoid-run-finds-point.md) within $2(n+1) \ln(\mathrm{vol}\, E_0 / \mathrm{vol}\, P)$ steps.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, the remark after Claim 7.2.
