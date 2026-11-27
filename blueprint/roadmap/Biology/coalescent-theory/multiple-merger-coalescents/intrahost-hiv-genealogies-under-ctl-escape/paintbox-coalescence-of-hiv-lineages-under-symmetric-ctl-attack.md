# Paintbox coalescence of HIV lineages under symmetric CTL attack

**Model.** CTLs attack $\mathbf e$ viral epitopes. An infected-cell variant is a binary word of length $\mathbf e$ (a $1$ marks an escape mutation at that epitope); on the *linear escape graph* the variants are $0\cdots0,\ 10\cdots0,\ 110\cdots0,\dots,1\cdots1$, and the *variant class* $\mathcal E_i$ consists of the variants with $i$ escapes. Under symmetric attack a variant in $\mathcal E_i$ dies at rate $k_v = 1 + (\mathbf e - i)\Delta k$ (time in units of the infected-cell lifetime, $\Delta k$ the killing rate per epitope). With target-cell density $h$ and population scale $\mathbb E$,

$$\frac{dh}{dt} = g\Big(1 - h - \sum_{v'}e_{v'}h\Big), \qquad de_v = \frac1{\mathbb E}\Big(dP(\gamma\mathbb E e_vh) - dP(k_v\mathbb E e_v) + \sum_{v'\in\mathcal P(v)}dP(\mu\gamma\mathbb E e_{v'}h)\Big),$$

where the $dP(\cdot)$ are independent Poisson increments with the indicated rates, $\gamma$ is the infection rate, $\mu$ the per-infection mutation probability and $\mathcal P(v)$ the parents of $v$ (variants one escape away). The **small population limit** (SPL) is $\mathbb E\to\infty$, $\mu\to0$ with $\mu\mathbb E\to\infty$ and $\mu^3\mathbb E^2\to0$. Sample $n$ infected cells after full escape and let $\Pi(0)$ be the partition of the sample induced by common ancestry at time $0$.

**Paintbox.** For $i = 0,\dots,\mathbf e - 2$ let $\Gamma^{(i)} = e^{2W_1}W_2\,B\big(2\Delta k/k_i\big)$, with $W_1, W_2$ independent standard exponentials and $B(p)$ an independent Bernoulli$(p)$ variable. Given $A > 0$, define the random partition $\Xi_{A,i}$ of a set $S$: draw $K\sim\mathrm{Poisson}(A)$ and i.i.d. weights $\Gamma_1,\dots,\Gamma_K\sim\Gamma^{(i)}$, paint each element of $S$ independently with color $j$ with probability $\Gamma_j/\sum_{j'}\Gamma_{j'}$, and group elements of the same color.

**Theorem.** For the linear escape graph and every partition $\Delta$ of the $n$ sampled lineages,

$$\lim_{\mathrm{SPL}}\mathbb P\big(\Pi(0) = \Delta\big) = \mathbb P\Big(\Big(\prod_{i=0}^{\mathbf e-2}\Xi_{A,i}\Big)\big(\Pi(T_{\mathrm{sample}})\big) = \Delta\Big) + O\Big(\frac1A\Big),$$

where $\Pi(T_{\mathrm{sample}})$ is the partition into singletons and the product denotes successive application of independent paintboxes (blocks painted the same color are merged): going backwards in time, lineages are merged by one paintbox per escape sweep (the color of a lineage being the escape mutation event founding its subclone). An analogous statement, with modified paintboxes $\Xi_{A,i}$ that account for interactions between the variants within a class, holds for the full escape graph.

## Expansion

In the SPL the dynamics are a sequence of sweeps: while class $\mathcal E_{i-2}$ dominates, class $\mathcal E_{i-1}$ grows at relative rate $\Delta k$ and spawns $\mathcal E_i$ variants by rare mutations, which grow at relative rate $2\Delta k$ (they escape one more epitope). This is a generalized Luria–Delbrück phase. The mutations founding the next class arrive as a Poisson process, each one survives initial stochastic loss with probability about $2\Delta k/k_i$ (the Bernoulli factor), and its descendant number at the end of the phase is proportional to $e^{2W_1}W_2$ from the random arrival time and branching-process growth; $\mu^3\mathbb E^2\to0$ prevents a spawned variant from itself spawning within the same phase. Sampled cells of the next class pick their founding mutation with probability proportional to its share of descendants, which is the paintbox, and concatenating phases gives the product formula; the $O(1/A)$ term controls the contribution of mutation events beyond a large typical number.

## Sources

- Sivan Leviyang, "The coalescence of intrahost HIV lineages under symmetric CTL attack", *Bulletin of Mathematical Biology* 74 (2012), 1818–1856, <https://doi.org/10.1007/s11538-012-9737-x>; preprint arXiv:1108.0686, <https://doi.org/10.48550/arXiv.1108.0686>. Numbering of the arXiv version: Section 2 (escape graphs, stochastic ODE, symmetric attack), Section 3 (small population limit, Definition of $\Xi_{A,i}$ for the linear and full escape graphs, Theorems 3.1 and 3.2), Sections 5–6 (spawning-phase dynamics and lineage construction for the linear and full escape graphs).
