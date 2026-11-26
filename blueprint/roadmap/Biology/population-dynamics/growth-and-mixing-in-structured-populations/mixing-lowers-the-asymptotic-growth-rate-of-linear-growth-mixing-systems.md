# Mixing lowers the asymptotic growth rate of linear growth–mixing systems

Consider $n$ sites (patches, tissue compartments, habitats) with site-specific growth or decay rates $g_i \in \mathbb R$, collected in the diagonal matrix $G = \mathrm{diag}(g_1,\dots,g_n)$, and movement between sites described by a real matrix $M$ with non-negative off-diagonal entries (an **ML-matrix**, or essentially non-negative matrix). For a mixing intensity $m \ge 0$ the population vector obeys

$$\dot x(t) = (G + mM)\,x(t), \qquad x(t) = e^{(G + mM)t}x(0),$$

whose asymptotic growth rate is the **spectral abscissa** $r(G + mM) = \max_i \operatorname{Re}\lambda_i(G + mM)$, which for ML-matrices is the Perron root.

**Theorem (growth and mixing).** For $m \ge 0$,

$$\frac{d}{dm}\, r(G + mM) \le r(M),$$

with equality if and only if $G = cI$ for some $c \in \mathbb R$, or $M$ is reducible and $G$ is constant on the relevant diagonal blocks of the Frobenius normal form of $M$.

**Corollaries.**

1. (Measure-preserving mixing) If mixing conserves total quantity ($\mathbf 1^\top M = 0$, so $r(M) = 0$), then $r(G + mM)$ is non-increasing in $m$, strictly decreasing for irreducible $M$ and $G \neq cI$: more mixing slows net growth, or speeds net decay.
2. (Lossy mixing) If quantity is lost in transit ($\mathbf 1^\top M \le 0$, $\neq 0$), then $\tfrac{d}{dm} r(G + mM) < 0$ for every diagonal $G$.
3. (Bounds) If $r(M) = 0$, then $r(G + mM) \in [\min_i g_i, \max_i g_i]$.
4. (Stability) If $r(M) \le 0$ and the zero solution is unstable at some $m^*$, it is unstable for all $0 \le m \le m^*$.
5. (Heterogeneity) For small enough $m$, $r(G + mM) > \frac1n \sum_i g_i$: heterogeneous growth beats average growth under weak mixing.

**Theorem (convexity).** For irreducible $M$, $m \mapsto r(G + mM)$ is convex, strictly unless $G = cI$.

This is the continuous-time counterpart of Karlin's theorem that $\rho\big(((1-\alpha)I + \alpha P)D\big)$ decreases in $\alpha$ for an irreducible stochastic migration matrix $P$ and positive fitnesses $D \neq dI$, and it underlies the reduction principle for the evolution of dispersal and source–sink results.

## Depends on

- [Perron-vector inequality for essentially non-negative matrices](perron-vector-inequality-for-essentially-non-negative-matrices.md)
- [Reduction principle for modifiers of transmission](../../population-genetics/selection-migration-and-transmission/modifier-theory-and-the-evolution-of-recombination/reduction-principle.md)

## Expansion

For irreducible $M$, the derivative of a simple Perron root is $\tfrac{d}{dm} r(G + mM) = u^\top M v$, where $u, v$ are the left and right Perron vectors of $G + mM$ normalized by $u^\top v = 1$. Writing $G + mM = m(M + G/m)$, the Perron-vector inequality $u(A + D)^\top A\, v(A + D) \le r(A)$ applied with $A = M$ and $D = G/m$ gives $u^\top M v \le r(M)$, with equality only when $G$ is a multiple of $I$. The corollaries follow by inserting $r(M) = 0$ or $r(M) < 0$ (subinvariance) and integrating the derivative bound. Convexity comes from Cohen's convexity of the Perron root in the diagonal entries, extended by Friedland to ML-matrices.

## Sources

- Lee Altenberg, "Karlin Theory On Growth and Mixing Extended to Linear Differential Equations", arXiv (2010). Karlin's Theorem 5.2 as restated, Main Result, Theorem 6 (Growth and Mixing), Corollaries 7, 8, 11, 12, Lemma 9, Theorem 10, Theorem 13 (Convexity). <https://doi.org/10.48550/arXiv.1006.3147>
