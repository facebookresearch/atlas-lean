# Clock and epoch lengths of the variable-size coalescent

Let $\lambda(u) = 1/f(u)$ be the coalescence intensity of a population whose relative size $f$ is strictly positive, and $\Lambda(t) = \int_0^t \lambda(u)\, du$ its integrated intensity. Tavaré (2004, Section 2.4) shows that the ancestral process $A^v_n$ of a sample of $n$ is a time-inhomogeneous pure death process that jumps from $j$ to $j - 1$ at rate $j(j - 1)\lambda(t)/2$ (equation (2.4.7)), and that it is the constant-size ancestral process $A_n$ run on the clock $\Lambda$: $A^v_n(t) = A_n(\Lambda(t))$ (equation (2.4.8)), so $P(A^v_n(t) = j) = g_{nj}(\Lambda(t))$ with Tavaré's formula $g_{nj}$. If $T_n, \dots, T_2$ are the constant-size holding times and $S_j = T_n + \dots + T_j$, the variable-size holding times are

$$T^v_n = \Lambda^{-1}(S_n), \qquad T^v_j = \Lambda^{-1}(S_j) - \Lambda^{-1}(S_{j+1}), \quad j = n - 1, \dots, 2$$

(equation (2.4.9)), with joint density $\prod_{j=2}^n \binom j2 \lambda(s_j)\exp\bigl(-\binom j2(\Lambda(s_j) - \Lambda(s_{j+1}))\bigr)$ in the partial sums $s_j = t^v_j + \dots + t^v_n$ of the variable-size holding times, with $s_{n+1} = 0$ (equation (2.4.6)). Unlike the independent exponentials of the constant-size case, the $T^v_j$ are in general dependent, since each is a function of several partial sums $S_j$; $(S_{n+1} = 0, S_n, \dots, S_2)$ is a Markov chain. Section 2.4 assumes $\Lambda(t) \to \infty$, so that a common ancestor is reached with probability one; when $\Lambda(\infty) < \infty$ two lineages never coalesce with probability $e^{-\Lambda(\infty)} > 0$, by $P(T_2 > t) = e^{-\Lambda(t)}$ (equation (2.4.4)).

## Depends on

- [Cumulative coalescence intensity](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/cum-rate.md)
- [Tavaré's formula for the number of ancestral lineages](../../../Biology/coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)

## Expansion

1. The clock $\Lambda$: continuity, strict monotonicity when $f < \infty$, and the inverse $\Lambda^{-1}$ on $[0, \Lambda(\infty))$.
2. The time-changed process $A_n(\Lambda(\cdot))$ and its identification with the pure death process of rates $\binom j2\lambda(t)$.
3. The holding times $T^v_j$ as functions of the constant-size partial sums, their joint density (2.4.6), and an explicit history for which two of them are dependent.
4. Clocks with $\Lambda(\infty) < \infty$: the probability that the sample never reaches its most recent common ancestor, and the defective law of the holding times.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Section 2.4, equations (2.4.4), (2.4.6)–(2.4.9).
- Original result: R. C. Griffiths and S. Tavaré, Sampling theory for neutral alleles in a varying environment, Philos. Trans. R. Soc. Lond. B 344 (1994), 403–410. <https://doi.org/10.1098/rstb.1994.0079> The time-change representation follows Tavaré (2004), Section 2.4.
