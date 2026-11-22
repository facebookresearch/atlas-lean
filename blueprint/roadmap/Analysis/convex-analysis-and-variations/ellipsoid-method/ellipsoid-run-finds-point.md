# The ellipsoid method finds a point

In a run of the central-cut ellipsoid method as in the [invariant](ellipsoid-run-invariant.md), if

$$
e^{-N/(2(n+1))}\, \mathrm{vol}\, E_0 \le \mathrm{vol}\, P , \qquad\text{i.e.}\qquad N \ge 2(n+1) \ln \frac{\mathrm{vol}\, E_0}{\mathrm{vol}\, P} ,
$$

then one of the centres $a_0, \dots, a_N$ lies in $P$. Otherwise $P \subseteq E_{N+1}$ and $\mathrm{vol}\, P \le e^{-(N+1)/(2(n+1))} \mathrm{vol}\, E_0 < e^{-N/(2(n+1))} \mathrm{vol}\, E_0$, using that $E_0$ has [positive](volume-ellipsoid-ne-zero.md) and [finite](volume-ellipsoid-ne-top.md) volume. The hypothesis forces $\mathrm{vol}\, P > 0$. Turning this into Khachiyan's polynomial-time algorithm for rational linear programs needs bounds on $\mathrm{vol}\, E_0 / \mathrm{vol}\, P$ in terms of the encoding length, perturbation of lower-dimensional polyhedra and finite-precision arithmetic.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, the remark after Claim 7.2 ("If P is nonempty then the Ellipsoid Algorithm should find x ∈ P in at most $2(n + 1) \ln(\mathrm{Vol}(E_0)/\mathrm{Vol}(P))$ steps").
