# Clone-size-indexed progenitor counts and an exact Luria-Delbrück law

**Homeostatic clones.** A progenitor cell (P) divides into PP, PD or DD with probabilities $a$, $b$, $c$ ($a+b+c = 1$), where D cells are differentiated and never divide. Index the process by the clone size $n$ (each division adds one cell) rather than by time; then the number $k$ of progenitors performs a lattice walk with up, flat and down steps of probabilities $a$, $b$, $c$, absorbed at $0$ (gambler's ruin). Starting from one progenitor, let $P_{n,k}$ be the probability that the clone has $k$ progenitors when it has $n$ cells.

**Theorem 1.**

*(1)* For $k \ge 1$,

$$P_{n,k} = \sum_{i=0}^{\lfloor (n-k)/2\rfloor}\binom{n-1}{k+2i-1}\Big(\binom{k+2i-1}{i} - \binom{k+2i-1}{i-1}\Big)a^{k+i-1}b^{n-k-2i}c^i,$$

and the probability that a clone of size $n$ is fully differentiated is the weighted Motzkin number

$$P_{n,0} = \sum_{i=0}^{\lfloor (n-2)/2\rfloor}\binom{n-2}{2i}\Big(\binom{2i}{i} - \binom{2i}{i-1}\Big)a^ib^{n-2-2i}c^{i+1}.$$

*(2)* The generating function of the absorption probabilities is

$$G(t) = \sum_{n}P_{n,0}t^n = \frac{1 - bt - \sqrt{(bt-1)^2 - 4act^2}}{2a},$$

and $F(x,t) = \sum_{n,k}P_{n,k}x^kt^n$ has an explicit algebraic form. Evaluating at $t=1$ gives the probability that a single progenitor's lineage eventually differentiates completely, $G(1) = \min\{a,c\}/a$, i.e. $1$ if $c \ge a$ and $c/a$ if $c < a$.

**Exact Luria-Delbrück recursion.** In a pure-birth (Yule) clone started from one non-mutant cell, a dividing non-mutant produces a mutant daughter with probability $\mu_1$ (otherwise two non-mutants, probability $\mu_0 = 1-\mu_1$), and mutants breed true. With $p^{(k)}_m$ the probability of $m$ mutants among $k$ cells, $p^{(1)}_0 = 1$ and

$$p^{(k)}_m = \Big(\frac{m-1}{k-1} + \frac{k-m}{k-1}\mu_1\Big)p^{(k-1)}_{m-1} + \frac{k-1-m}{k-1}\mu_0\,p^{(k-1)}_m,$$

with mean $E^{(k)}_1 = \mu_1\sum_{u=1}^{k-1}\prod_{r=k-u+1}^{k-1}(1 + \mu_0/r)$.

## Expansion

Because division outcomes do not depend on division times, indexing by clone size removes time entirely: the progenitor count is a Motzkin-type path, and the ballot-type factor $\binom{k+2i-1}{i} - \binom{k+2i-1}{i-1}$ counts paths that stay positive. The same idea turns the Luria-Delbrück problem into a Pólya-urn-like recursion on the number of cells instead of a time-dependent generating function, giving exact finite-size distributions of mutant counts; selection enters by weighting which cell divides by its division rate. Clone-size data from lineage tracing can then be fitted without knowing clone ages.

## Sources

- A. Roshan, P. H. Jones and C. D. Greenman, "An Exact, Time-Independent Approach to Clone Size Distributions in Normal and Mutated Cells", J. R. Soc. Interface 11 (2014) 20140654 (Corollary 2.2); preprint arXiv:1311.5769 (2013), Section 2 (Theorems 2.1 and 2.2, Corollaries 2.1 and 2.2) and Section 3 (Theorems 3.1 and 3.3), <https://doi.org/10.48550/arXiv.1311.5769>.
