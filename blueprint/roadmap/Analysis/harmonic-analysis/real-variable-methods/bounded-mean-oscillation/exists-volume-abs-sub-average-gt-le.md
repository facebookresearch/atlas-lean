# John–Nirenberg inequality

There is an absolute constant $c > 0$ with the following property. Let $f \colon \mathbb{R} \to \mathbb{R}$ be locally integrable and $B > 0$ with $\frac{1}{b-a} \int_a^b |f - f_{[a,b]}| \le B$ for all $a < b$, where $f_{[a,b]}$ is the average of $f$ over $[a, b]$. Then for every interval $I = [a, b]$ with $a < b$ and every $\alpha > 0$,

$$\big|\{x \in I : |f(x) - f_I| > \alpha\}\big| \le 2\,|I|\, e^{-\alpha / (c B)}.$$

This is inequality (2.1) of A. K. Lerner, *A "local mean oscillation" decomposition and some its applications*, lecture notes (https://u.math.biu.ac.il/~lernera/paseky.pdf), with $n = 1$ and $\|f\|_{\mathrm{BMO}}$ replaced by any upper bound $B$ (equivalent, since the right-hand side increases with $B$); Lerner attributes it to F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math. 14 (1961), 415–426. The source is stated on $\mathbb{R}^n$ with cubes; this is the one-dimensional case, weaker than the source. The hypothesis $B > 0$ excludes only a trivial case: if $B = 0$ then $f$ is a.e. constant on every interval. The hypotheses are satisfiable non-trivially, for example by $f(x) = \log|x|$. The averages are Bochner averages; they are genuine averages because $f$ and $|f - f_I|$ are integrable on bounded intervals.

## Background

- [Calderón–Zygmund decomposition, dyadic form](../dyadic-maximal-function/calderon-zygmund.md): the classical proof applies the decomposition to $(f - f_I) \mathbf{1}_I$ at height $2B$ and iterates on the selected intervals, gaining a factor $1/2$ in measure at each step.

## Sources

- A. K. Lerner, *A "local mean oscillation" decomposition and some its applications*, lecture notes (https://u.math.biu.ac.il/~lernera/paseky.pdf), §2.1, inequality (2.1) (a secondary source).
- F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math. 14 (1961), 415–426 (original; not read for this page).
