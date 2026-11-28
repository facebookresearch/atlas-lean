# The rendering equation as a fixed-point equation

Let $X$ be a real Banach space of radiance functions, $E \in X$ an emission term and $T : X \to X$ a bounded linear transport operator with $\|T\| \le c < 1$. Then the rendering equation $I = E + TI$ has the unique solution $I = \sum_{k \ge 0} T^k E$ in $X$. Keeping the terms $k=0,\ldots,K$ gives error at most $c^{K+1}\|E\|/(1 - c)$. Pointwise loss of energy is not sufficient: on the space of bounded sequences indexed from zero, the diagonal operator with entries $1 - 1/(n+1)$ has norm $1$, and for constant unit emission the coordinate equations force $I_n = n+1$, so there is no bounded solution.

## Sources

- J. T. Kajiya, "The rendering equation", *SIGGRAPH 1986*, *Computer Graphics* 20(4):143–150, 1986
- E. Veach, *Robust Monte Carlo Methods for Light Transport Simulation*, PhD thesis, Stanford University, 1997, Section 4.4
