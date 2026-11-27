# Coboundary expansion of the complete complex

Let $\Delta_n^{(d)}$ be the complete $d$-dimensional complex on $n$ vertices with the uniform weighting. Then for every $0 \le i < d$,

$$
h^i\bigl(\Delta_n^{(d)}\bigr) \ge \frac{n}{n-i-1} \ge 1,
$$

that is, every $i$-cochain $f$ satisfies $\|\delta_i f\| \ge \operatorname{dist}(f, B^i)$ in the normalized norms. In particular the complete complex is a $1$-coboundary expander in every dimension below $d$.

## Proof sketch

Use the cone construction: for each vertex $v$, the cochain $f_v = f + \delta(\iota_v f)$, where $\iota_v$ contracts with $v$, differs from $f$ by a coboundary and is supported on faces containing $v$ only through $\delta f$. Averaging $\|f_v\|$ over $v$ expresses it as a multiple of $\|\delta f\|$, giving a coboundary within normalized distance $\|\delta f\|$ of $f$.

## Depends on

- [Coboundary expansion of a simplicial complex](coboundary-expansion.md)
- [Cochains and the coboundary operator over F_2](cochains-coboundary.md)

## Sources

- N. Linial, R. Meshulam, "Homological connectivity of random 2-complexes", Combinatorica 26 (2006) 475-487.
- M. Gromov, "Singularities, expanders and topology of maps. Part 2: from combinatorics to topology via algebraic isoperimetry", Geometric and Functional Analysis 20 (2010) 416-526.
