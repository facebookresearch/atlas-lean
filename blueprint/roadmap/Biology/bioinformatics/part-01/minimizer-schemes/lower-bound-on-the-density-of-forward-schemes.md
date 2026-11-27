# Lower bound on the density of forward schemes

Let $\Sigma$ have size $\sigma$ and fix $k, w \ge 1$. A local scheme $f : \Sigma^{w+k-1} \to \{0,\dots,w-1\}$ is a **forward scheme** if for every window $\omega$ and every $x \in \Sigma$,

$$f(\omega[1, w+k-2] \cdot x) \ge f(\omega) - 1,$$

i.e. the selected position never moves backwards when the window slides by one base. Every minimizers scheme is a forward scheme. Let $d_{f,k,w}$ denote the density (expected fraction of selected positions on an i.i.d. uniform sequence).

**Lemma.** If $X, Y$ are independent, identically distributed random variables with values in $\{0, \dots, w-1\}$, then $\Pr[X \ge Y] \ge \tfrac12 + \tfrac{1}{2w}$.

**Theorem.** Every forward scheme satisfies

$$d_{f,k,w} \;\ge\; \frac{1.5 + \max\!\left(0, \left\lfloor \frac{k-w}{w} \right\rfloor\right) + \frac{1}{2w}}{w+k}.$$

In particular the density factor $d_{f,k,w}(w+1)$ of any forward scheme is at least about $1.5$ for large $w$.

## Expansion

The lemma follows from $\Pr[X > Y] = \Pr[X < Y]$ and $\Pr[X = Y] = \sum_j p_j^2 \ge 1/w$ by Cauchy–Schwarz. For the theorem, take two windows $\omega_1, \omega_2$ separated by a gap of two bases, so that on a de Bruijn sequence of high order they are independent and identically distributed; let $X_i = f(\omega_i)$ be their selected offsets. Among the $w+k$ windows starting strictly between them, at least one must select a new $k$-mer (the $k$-mer chosen in $\omega_1$ drops out of the window starting just after it), and extra selections are forced when the gap $\Delta$ between the two chosen $k$-mers is large, since a forward scheme must select a $k$-mer in every stretch of $w$ consecutive windows. The extra windows are charged with probability at least $\Pr[X_2 \ge X_1] \ge \tfrac12 + \tfrac1{2w}$, giving the expected count $1.5 + \lfloor (k-w)/w \rfloor^+ + 1/(2w)$ selections per $w + k$ windows. This refines the earlier bound of Schleimer, Wilkerson and Aiken; local schemes that are not forward can beat it for some parameters (e.g. $k = 2$, $w = 4$, found by integer programming).

## Sources

- G. Marçais, D. DeBlasio, C. Kingsford, "Asymptotically optimal minimizers schemes", Bioinformatics 34(13) (2018) i13–i22, Section 2.1.2, Lemma 2 and Theorem 3, <https://doi.org/10.1093/bioinformatics/bty258>, PMCID PMC6037127.
