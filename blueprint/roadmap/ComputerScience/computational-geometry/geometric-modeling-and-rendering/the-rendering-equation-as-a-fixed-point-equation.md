# The rendering equation as a fixed-point equation

Let $X$ be a Banach space of radiance functions, $E \in X$ an emission term and $T : X \to X$ a bounded linear transport operator with $\|T\| \le c < 1$. Then the rendering equation $I = E + TI$ has the unique solution $I = \sum_{k \ge 0} T^k E$ in $X$, and truncating the series after $K$ bounces has error at most $c^{K+1}\|E\|/(1 - c)$. Pointwise loss of energy is not sufficient: on the space of bounded sequences, the diagonal operator with entries $1 - 1/n$ has norm $1$, and for $E = 1$ the formal solution $I_n = n$ is unbounded.

## Sources

- J. T. Kajiya, "The rendering equation", *SIGGRAPH 1986*, *Computer Graphics* 20(4):143–150, 1986
- E. Veach, *Robust Monte Carlo Methods for Light Transport Simulation*, PhD thesis, Stanford University, 1997, Section 4.4
