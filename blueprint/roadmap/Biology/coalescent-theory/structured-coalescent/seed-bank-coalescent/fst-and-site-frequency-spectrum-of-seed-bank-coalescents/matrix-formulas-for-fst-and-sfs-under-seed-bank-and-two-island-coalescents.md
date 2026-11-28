# Matrix formulas for F_ST and the expected SFS under seed-bank and two-island coalescents

**Models.** Lineages are either in population 1 (active plants, or island 1) or population 2 (dormant seeds, or island 2), with relative size ratio $K$ (population 2 has size $N/K$). Time is in units of $N$ generations. In the **strong seed-bank coalescent** ($\mathrm S$), active lineages become dormant at rate $c$, dormant lineages resuscitate at rate $cK$, each pair of active lineages coalesces at rate $1$, and dormant lineages never coalesce. In the **two-island structured coalescent** ($\mathrm{TI}$) the same migration holds but pairs in population 2 also coalesce at rate $1/K$. Write $\alpha^{\mathrm S}=0$, $\alpha^{\mathrm{TI}}=1/K$. For a pair of lineages, order the states as (both in 1), (one in each), (both in 2), and let

$$
S^{\mathrm I}=\begin{pmatrix}-(2c+1)&2c&0\\ cK&-(cK+c)&c\\ 0&2cK&-(2cK+\alpha^{\mathrm I})\end{pmatrix},\qquad s^{\mathrm I}=\begin{pmatrix}1\\0\\ \alpha^{\mathrm I}\end{pmatrix},\qquad \mathrm I\in\{\mathrm S,\mathrm{TI}\},
$$

the sub-generator and exit (coalescence) vector of the pair process. **Wright's fixation index** is $F_{ST}=(p_0-\bar p)/(1-\bar p)$, with $p_0$ the identity probability of two genes from one subpopulation (chosen proportionally to size) and $\bar p$ that of two genes sampled from the whole population.

**Proposition ($F_{ST}$, Proposition 2.1).** Under the infinite-alleles model with mutation rates $u$ in population 1 and $u'$ in population 2, let $A=\mathrm{diag}(-2u,\,-(u+u'),\,-2u')$,

$$
\pi_0=\Bigl(\frac{K}{1+K},\,0,\,\frac{1}{1+K}\Bigr),\qquad \bar\pi=\Bigl(\frac{K^2}{(1+K)^2},\,\frac{2K}{(1+K)^2},\,\frac{1}{(1+K)^2}\Bigr).
$$

Then $p_0^{\mathrm I}=\pi_0(-A-S^{\mathrm I})^{-1}s^{\mathrm I}$, $\bar p^{\mathrm I}=\bar\pi(-A-S^{\mathrm I})^{-1}s^{\mathrm I}$ and $F_{ST}^{\mathrm I}=(p_0^{\mathrm I}-\bar p^{\mathrm I})/(1-\bar p^{\mathrm I})$. Here $-A=\mathrm{diag}(2u,\,u+u',\,2u')$ holds the total mutation rates of the three pair states. The source prints $(A-S^{\mathrm I})^{-1}$ with the same $A$, a sign slip: for $\mathrm S$ with $c=1$, $K=2$, $u=u'=0.3$ that expression gives $p_0\approx-1.50$, while $\pi_0(-A-S^{\mathrm S})^{-1}s^{\mathrm S}\approx0.412$ is the identity probability.

**Proposition (expected SFS, Proposition 2.2).** Under the infinite-sites model with mutation rates $u,u'$, take a sample of $k$ genes. The $k$-lineage block-counting chain has states $a=(a_1,\dots,a_k,a_{k+1},\dots,a_{2k})$ in the source's state space $E$, where $a_i$ and $a_{k+i}$ are the numbers of lineages in population 1 and in population 2 that subtend exactly $i$ sampled genes. Lineages move and coalesce at the rates of model $\mathrm I$, and the chain is absorbed when one lineage subtends all $k$ genes. Write $S^{\mathrm I}_k$ for its sub-generator on the transient states (for $k=2$ it is $S^{\mathrm I}$ above) and $\pi$ for the initial distribution. The expected number of sites at which the mutant is carried by $i$ of the $k$ genes is

$$
\mathbb E_\pi\bigl[\zeta^{(k)}_i\bigr]=\pi\,(-S^{\mathrm I}_k)^{-1}r_i,\qquad i=1,\dots,k-1,
$$

where $r_i(a)=u\,a_i+u'\,a_{k+i}$ is the total mutation rate on branches subtending exactly $i$ sampled genes in state $a$.

## Depends on

- [Seed-bank coalescent](../seed-bank-coalescent-active-dormant-lineages.md)
- [Structured coalescent for n lineages with a general migration matrix](../../structured-coalescent-for-n-lineages-with-a-gene.md)

## Expansion

Two genes are identical by descent under infinite alleles iff no mutation falls on either lineage before coalescence; with $R_{2,0},R_{1,1},R_{0,2}$ the times spent in the three pair states, $p=\mathbb E[e^{-2uR_{2,0}-(u+u')R_{1,1}-2u'R_{0,2}}]$. The pair process is a transient Markov chain absorbed at coalescence with exit vector $s$, so this Laplace transform of accumulated rewards is the phase-type formula $\pi(-A-S)^{-1}s$: the reward rates $-A$ act as killing rates added to the exit rates. Likewise the expected total branch length subtending $i$ genes weighted by mutation rates is the expected accumulated reward $\pi(-S)^{-1}r_i$ of the absorbing chain (Green's matrix $(-S)^{-1}$ gives expected occupation times). Because dormant lineages in $\mathrm S$ cannot coalesce, $F_{ST}$ and the SFS can separate $\mathrm S$ from $\mathrm{TI}$ for some parameter ranges; full-likelihood pseudo-marginal MCMC separates all models under moderate stratification.

## Sources

- J. Blath, E. Buzzoni, J. Koskela and M. Wilke Berenguer, "Statistical tools for seed bank detection", arXiv:1907.13549 (2019), Section 1 (models S and TI), Section 2 (definition of $F_{ST}$, Propositions 2.1–2.2), <https://doi.org/10.48550/arXiv.1907.13549>; published in *Theoretical Population Biology* 132 (2020), 1–15, <https://doi.org/10.1016/j.tpb.2020.01.001>.
