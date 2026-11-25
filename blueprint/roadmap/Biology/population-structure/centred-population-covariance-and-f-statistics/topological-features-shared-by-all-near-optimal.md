# Admixture of a population is not a robust feature of exact three-population fits

Fix a finite set $\mathcal P$ of populations, a finite set $\iota$ of f2, f3 or f4 statistics on $\mathcal P$, estimated values $f\in\mathbb R^\iota$ and a positive definite matrix $Q$. A candidate topology $\mathcal T$ is an admixture graph on $\mathcal P$ with a parameter set $\Theta_{\mathcal T}$ of edge lengths and admixture proportions; each $\theta\in\Theta_{\mathcal T}$ determines a drift model and so predicted statistics $g_{\mathcal T}(\theta)\in\mathbb R^\iota$. With the [qpGraph score](../fitting-admixture-graphs-by-least-squares/score-s1.md) $S_1$, put $S(\mathcal T)=\sup_{\theta\in\Theta_{\mathcal T}}S_1(g_{\mathcal T}(\theta))$. For a family $\mathfrak F$ of candidate topologies with $S^*=\sup_{\mathcal T\in\mathfrak F}S(\mathcal T)$ finite and $\varepsilon\ge0$, the $\varepsilon$-optimal set is

$$O_\varepsilon=\{\mathcal T\in\mathfrak F:\ S(\mathcal T)\ge S^*-\varepsilon\}.$$

A topological feature is a property of topologies; it is *robust at $\varepsilon$* if every member of $O_\varepsilon$ has it.

**Theorem.** Let $\mathcal P=\{A,B,C\}$ and let $\mathfrak F$ contain the three-population admixture topology $\mathcal T_{\mathrm{adm}}$, with the [admixture weights](admix-weight.md), $\alpha\in[0,1]$ and lengths $a,b,c\ge0$, and the star topology $\mathcal T_\star$, with the [star weights](star-weight.md) and nonnegative lengths. Suppose the statistics are exact for an admixture model, $f=g_{\mathcal T_{\mathrm{adm}}}(\alpha,a,b,c)$, with

$$0\le\alpha\le1,\qquad a,b\ge0,\qquad c\ge\alpha(1-\alpha)(a+b),$$

the last condition being $f_3(C;A,B)\ge0$. Then $S^*=0$, both $\mathcal T_{\mathrm{adm}}$ and $\mathcal T_\star$ lie in $O_0$, and the feature "$C$ is admixed" is not robust at $\varepsilon=0$, hence at no $\varepsilon\ge0$.

Indeed $S_1\le0$ with equality at $g=f$, which $\mathcal T_{\mathrm{adm}}$ attains. The [matching star lengths](star-len.md) $\ell_\star=((1-\alpha)(a+b),\ \alpha(a+b),\ c-\alpha(1-\alpha)(a+b))$ are [nonnegative](star-len-nonneg.md), the [star and admixture models have equal f2](f2-star-eq-f2-admix.md), and f3 and f4 are linear in f2, so $\mathcal T_\star$ predicts $f$ exactly as well. For example, $\alpha=1/2$ and $a=b=c=1$ give star lengths $(1,1,1/2)$ and an exact fit by a tree in which no population is admixed.

## Depends on

- [The qpGraph score S1](../fitting-admixture-graphs-by-least-squares/score-s1.md)
- [Lineage weights of the three-population admixture model](admix-weight.md)
- [Lineage weights of the three-population star tree](star-weight.md)
- [Edge lengths of the star tree matching an admixture model](star-len.md)
- [Nonnegativity of the matching star-tree edge lengths](star-len-nonneg.md)
- [Star tree and admixture model have equal f2](f2-star-eq-f2-admix.md)

## Proof depends on

- [Profiling the admixture proportions in the qpGraph fit](../fitting-admixture-graphs-by-least-squares/outer-optimization-over-admixture-proportions.md)
- [Which drift models have the f-statistics of a star tree](f-equivalence-classes-of-drift-models.md)
- [Star tree with matching lengths and admixture model have equal f3](f3-star-eq-f3-admix.md)
- [Star tree and admixture model have equal f4](f4-star-eq-f4-admix.md)

## Expansion

A full page proves the theorem from the f2 equality, the expressions of f3 and f4 in terms of f2, and the sign of $S_1$, and records the toy example. It should also treat estimated statistics with bounded error: for every $f$, $S(\mathcal T_\star)\ge S_1(g_{\mathcal T_{\mathrm{adm}}}(\alpha,a,b,c))$ for all admissible parameters with $c\ge\alpha(1-\alpha)(a+b)$, so whenever such parameters are $\varepsilon$-optimal for the admixture topology, the star is $\varepsilon$-optimal too.

## Sources

- R. Maier, P. Flegontov, O. Flegontova, U. Işıldak, P. Changmai and D. Reich, *On the limits of fitting complex models of population history to f-statistics*, eLife 12 (2023), e85492, <https://reich.hms.harvard.edu/sites/reich.hms.harvard.edu/files/inline-files/elife-85492-v2.pdf>, Abstract: inference is warranted only when all well-fitting models share topological features. The definitions and the exact three-population theorem above are derived here from the source's methodological criterion.
