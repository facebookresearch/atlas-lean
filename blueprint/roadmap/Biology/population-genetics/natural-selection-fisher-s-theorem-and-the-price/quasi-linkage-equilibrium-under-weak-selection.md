# Quasi-linkage equilibrium dynamics of allele frequencies under weak selection

Work in the setting of the [two-locus quasi-linkage equilibrium approximation](two-locus-quasi-linkage-equilibrium-approximatio.md): two loci with alleles $A,a$ and $B,b$, the [diploid viability-selection and meiosis map](two-locus-viability-selection-with-recombination.md) with autonomous symmetric viabilities $w_{ij}=1+\varepsilon a_{ij}$, $|a_{ij}|\le1$, $a_{14}=a_{23}$, and a constant recombination fraction $r\in[r_0,\frac12]$ with $r_0>0$. Let $p_t=(p_{A,t},p_{B,t})\in[0,1]^2$ be the allele-frequency vector in generation $t$, and $\hat x(p)=(p_Ap_B,p_Ap_b,p_ap_B,p_ap_b)$ the gamete vector in linkage equilibrium. For $y$ in the simplex put $a_i(y)=\sum_ja_{ij}y_j$ and $\bar a(y)=\sum_iy_ia_i(y)$. The LD-free selection field $g=(g_A,g_B)$ is

$$g_A(p)=\sum_{i\in\{1,2\}}\hat x_i(p)\bigl(a_i(\hat x(p))-\bar a(\hat x(p))\bigr),\qquad g_B(p)=\sum_{i\in\{1,3\}}\hat x_i(p)\bigl(a_i(\hat x(p))-\bar a(\hat x(p))\bigr),$$

the first-order allele-frequency change of the model evaluated at $D=0$.

**Statement.** There are constants $\varepsilon_0>0$ and $K$, depending only on $r_0$, such that for $0<\varepsilon\le\varepsilon_0$, every initial gamete vector, every permitted fitness array and every $t\ge T(\varepsilon)$, where $T(\varepsilon)$ is the time of part (b) of the quasi-linkage-equilibrium approximation,

$$\bigl\|p_{t+1}-p_t-\varepsilon\,g(p_t)\bigr\|_2\le K\varepsilon^2 .$$

**Neutral case.** For $\varepsilon=0$ the allele frequencies are constant, $p_{t+1}=p_t$, by part (a) of the quasi-linkage-equilibrium approximation; this case is exact and separate from the bound above.

The multilocus contraction of linkage disequilibrium, the multilocus quasi-linkage-equilibrium regime and Nagylaki's theorem that the change in mean fitness equals the genic variance up to $O(\varepsilon^3)$ are separate statements, not consequences of this page.

## Depends on

- [Two-locus quasi-linkage equilibrium approximation](two-locus-quasi-linkage-equilibrium-approximatio.md)
- [Diploid two-locus viability selection followed by meiosis](two-locus-viability-selection-with-recombination.md)

## Proof depends on

- [A uniform weak-selection bound on two-locus linkage disequilibrium](two-locus-ld-contraction-under-weak-selection.md)
- [Global existence and uniqueness for globally Lipschitz ODEs](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md), for comparing the recursion with the continuous-time LD-free flow $\dot p=g(p)$

## Expansion

A full proof page must establish the following.

- The exact allele-frequency recursion: since $e_1+e_2=e_1+e_3=0$, the recombination term cancels and $p_{A,t+1}-p_{A,t}=\varepsilon\,h_A(x_t)/(1+\varepsilon\bar a(x_t))$ with $h_A(y)=\sum_{i\in\{1,2\}}y_i(a_i(y)-\bar a(y))$, and similarly for $B$ with $\{1,3\}$.
- $g=h\circ\hat x$, and $h$ is Lipschitz on the simplex with a constant independent of the fitness array; since $x_t=\hat x(p_t)+D_te$, the error is at most $\varepsilon(L|D_t|\,\|e\|+C\varepsilon)$.
- $|D_t|=O(\varepsilon)$ for $t\ge T(\varepsilon)$, from part (b) of the quasi-linkage-equilibrium approximation. The weaker bound $|D_t|\le(1-r_0)^t/4+6\varepsilon/r_0$ of the [uniform LD bound](two-locus-ld-contraction-under-weak-selection.md) already gives $|D_t|=O(\varepsilon/r_0)$ after $O(\log(1/\varepsilon)/r_0)$ generations, so the full tracking estimate is not needed for this step.
- The neutral case, treated separately.

## Sources

- T. Nagylaki, *The evolution of multilocus systems under weak selection*, Genetics 134 (1993), 627–647, <https://pmc.ncbi.nlm.nih.gov/articles/PMC1205503/> (statement and proof).
- M. Kimura, *A stochastic model concerning the maintenance of genetic variability in quantitative characters*, Proc. Natl. Acad. Sci. USA 54 (1965), <https://doi.org/10.1073/pnas.54.3.731> (background: origin of quasi-linkage equilibrium).
