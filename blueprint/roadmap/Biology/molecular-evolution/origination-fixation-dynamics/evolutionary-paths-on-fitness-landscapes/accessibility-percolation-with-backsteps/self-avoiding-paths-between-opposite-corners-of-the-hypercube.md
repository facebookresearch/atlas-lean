# Number of self-avoiding paths between opposite corners of the hypercube

Let $a_L$ be the number of self-avoiding paths along the edges of the $L$-dimensional hypercube $\{0,1\}^L$ from $00\cdots0$ to $11\cdots1$ (paths of any length that never revisit a site).

**Theorem.**

$$\lim_{L\to\infty} \frac{\ln\ln a_L}{L} = \ln 2.$$

More precisely, there are constants $c, c' > 0$ such that for all large $L$

$$c \le \frac{\ln a_L}{2^L} \le c'\ln L.$$

So the number of self-avoiding corner-to-corner paths is doubly exponential in $L$, far larger than the $L!$ shortest paths.

## Expansion

The upper bound is elementary: a self-avoiding path visits at most $2^L$ sites and has at most $L$ choices at each step, so $a_L \le L^{2^L}$. The lower bound requires exhibiting $e^{c\,2^L}$ distinct self-avoiding corner-to-corner paths, i.e. paths that visit a positive fraction of all $2^L$ sites in many different orders; the paper gives this construction in a dedicated section. In accessibility percolation with backsteps these paths are the candidate mutational trajectories from the wild type to the antipodal genotype.

## Sources

- Julien Berestycki, Éric Brunet, Zhan Shi, "Accessibility percolation with backsteps", *ALEA Latin American Journal of Probability and Mathematical Statistics* 14 (2017), <https://doi.org/10.30757/ALEA.v14-04>; preprint arXiv:1401.6894, <https://doi.org/10.48550/arXiv.1401.6894>. Numbering of the arXiv version: Section 2 (Theorem 4) and Section 3 (its proof).
