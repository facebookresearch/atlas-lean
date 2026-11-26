# Quenched structured coalescent on a diploid pedigree with large migrations

**Model.** A diploid population is split into demes indexed by the vertex set $V$ of a graph with edge set $E$; deme $v$ has $N(v)$ individuals. In each generation, offspring in each deme choose two parents (possibly from other demes along edges $e \in E$), and offspring numbers may be very uneven: occasionally one or a few individuals of a deme produce a positive fraction $x \in \Delta$ of the next generation (sweepstakes reproduction), and occasionally a positive fraction $m_e \in [0,1]$ of a deme migrates along edge $e$ in one generation. The realized parent–offspring relations form the *pedigree* $\mathcal{A}_N$. Sample $n$ genes, follow their ancestral lineages through the pedigree (each gene picks one of its carrier's two parental genes with probability $1/2$), and let $\overline\chi^{N,n}$ be the resulting process of labeled partitions with deme labels, valued in $\mathcal{E}_n(V)$, with time measured in units of the coalescence time scale $c_N^{-1}$. *Annealed* means averaging over the pedigree; *quenched* means conditioning on it.

**Limit object.** A $\Psi$-driven $(\kappa,\mu)$-$n$-coalescent: let $\Psi$ be a Poisson point process on $[0,\infty)\times(\Delta^V\times[0,1]^E)$ with intensity $dt\otimes\Phi$. Between atoms of $\Psi$ the process is a structured Kingman coalescent, with pair-coalescence rates $\kappa$ inside demes and single-lineage migration rates $\mu$ along edges. At an atom $(t, x, m)$, every lineage in deme $v$ independently joins the large family $i$ with probability $x^v_i$ (lineages joining the same family merge, each family's genes then split between its parent's two copies), and lineages in the source deme of edge $e$ jump along $e$ with probability $m_e$. Averaging over $\Psi$ gives the annealed $(\Phi,\kappa,\mu)$-$n$-coalescent, whose generator is $K_n(\kappa) + M_n(\mu) + Q_n(\Phi)$.

**Theorem.** Under the paper's assumptions on initial sampling, continuity and comparability of deme sizes, rarity of large reproduction and migration events, convergence of migration probabilities, integrability of $\Phi$, and absence of total migrations:
1. (annealed) $\overline\chi^{N,n}$ converges in distribution in $\mathcal{D}(\mathbb{R}_+, \mathcal{E}_n(V))$ to a $(\Phi, \kappa, \mu)$-$n$-coalescent;
2. (quenched) the conditional law of $\overline\chi^{N,n}$ given the pedigree converges weakly in distribution to the conditional law of the $\Psi$-driven $(\kappa,\mu)$-$n$-coalescent given $\Psi$:
$$\mathbb{P}\big(\overline\chi^{N,n} \in \cdot \mid \mathcal{A}_N\big) \Longrightarrow \mathbb{P}\big(\chi^n \in \cdot \mid \Psi\big).$$

So the pedigree is remembered in the limit exactly through the times and sizes of its large reproduction and migration events; ordinary generations average out.

## Depends on

- [Structured coalescent for n lineages with a general migration matrix](../structured-coalescent/structured-coalescent-for-n-lineages-with-a-gene.md)
- [Coalescent limits of supercritical sampling with heavy-tailed potential offspring](../sweepstakes-reproduction-coalescents/supercritical-sampling-coalescent-limits.md)

## Expansion

Large events occur on the coalescent time scale and are finite in number on compact intervals, so the pedigree's large events converge to the Poisson process $\Psi$ (a weak-convergence criterion on the joint moments of family fractions and migration fractions identifies $\Phi$). Given the pedigree, lineages between large events see a sea of small families whose effect is a law of large numbers: pair coalescence and single migration at deterministic rates. At a large event, the conditional merger probabilities depend only on the event's family fractions, which match $q_n(x,m)$ in the limit. A coupling of the lineage processes on the pedigree with the $\Psi$-driven coalescent converts these statements into quenched weak convergence.

## Sources

- M. Newman, "The quenched coalescent for structured diploid populations with large migrations and uneven offspring distributions", arXiv:2601.21079 (2026), Definitions 3.13, 4.1, Theorem 3.14 and Theorem 4.3, <https://doi.org/10.48550/arXiv.2601.21079>.
