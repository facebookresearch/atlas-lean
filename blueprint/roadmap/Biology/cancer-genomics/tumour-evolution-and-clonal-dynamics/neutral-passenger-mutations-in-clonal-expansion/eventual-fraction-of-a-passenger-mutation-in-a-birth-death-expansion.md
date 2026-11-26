# Eventual fraction of a passenger mutation in a birth–death expansion

Consider a supercritical linear birth–death process in which every cell divides at rate $b$ and dies at rate $d$, with $0 \le d < b$, and write $\delta = d/b \in [0,1)$ for the death–birth ratio (the extinction probability of a single cell's lineage). Suppose a neutral mutation with a surviving lineage arises when there are $z \ge 1$ other (non-mutant) cells, and let $x$ be the fraction of mutant cells as $t \to \infty$ on the event of non-extinction.

**Distribution.** In the large-time approximation, where each surviving lineage grows like $e^{(b-d)t}V$ with independent exponential $V$, for $0 < \alpha < 1$

$$\Pr[x \le \alpha \mid z] \approx \sum_{i=1}^{z}\binom{z}{i}(1-\delta)^i\delta^{z-i}\bigl(1-(1-\alpha)^i\bigr) = 1 - \bigl(1-\alpha(1-\delta)\bigr)^z,$$

so $x$ has an atom $\Pr[x = 1 \mid z] = \delta^z$ (all $z$ other lineages die out) and density $f_z(\alpha) = (1-\delta)\,z\,\bigl(1-\alpha(1-\delta)\bigr)^{z-1}$ on $(0,1)$.

**Mean.**

$$\mathbb E[x \mid z] = \delta^z + \int_0^1 \alpha f_z(\alpha)\,d\alpha = \frac{1-\delta^{z+1}}{(1-\delta)(z+1)}.$$

For $\delta = 0$ this is $1/(z+1)$; for $\delta$ near $1$ it is much larger.

**Inverse problem.** For an observed subclonal fraction $\alpha \in (0,1)$, the maximum-likelihood estimate of the number of cells present when the mutation arose maximizes $f_z(\alpha)$ over $z$:

$$\hat z_{\mathrm{ML}} = -\frac{1}{\log\bigl(1-\alpha(1-\delta)\bigr)},$$

and with a geometric prior $p(z) = v(1-v)^{z-1}$, $v \ll 1$, the maximum a posteriori estimate is $\hat z_{\mathrm{MAP}} = -1/\bigl(\log(1-v) + \log(1-\alpha(1-\delta))\bigr) \approx \hat z_{\mathrm{ML}}$.

## Depends on

- [Limiting extinction probability in the supercritical case](../../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-lt.md)

## Expansion

Of the $z$ non-mutant cells, the number $i$ with surviving lineages is $\mathrm{Binomial}(z, 1-\delta)$. If $i = 0$ the mutant fixes. If $i \ge 1$, the mutant and non-mutant populations are asymptotically $e^{(b-d)t}V$ and $e^{(b-d)t}(V_1+\dots+V_i)$ with i.i.d. exponential $V, V_j$, so $x = V/(V+V_1+\dots+V_i)$ is $\mathrm{Beta}(1,i)$ with $\Pr[x \le \alpha] = 1-(1-\alpha)^i$. Summing over $i$ by the binomial theorem gives $1 - \bigl((1-\delta)(1-\alpha) + \delta\bigr)^z$. Differentiating $z\log(1-\alpha(1-\delta)) + \log z$ in $z$ and setting it to zero gives $\hat z_{\mathrm{ML}}$. Because $\hat z$ grows with $\delta$, a mutation observed at a given frequency arose in a much larger population when cell death is high.

## Sources

- I. Bozic, J. M. Gerold, M. A. Nowak, "Quantifying clonal and subclonal passenger mutations in cancer evolution", PLoS Computational Biology 12 (2016) e1004731, Methods ("Eventual fraction and time of appearance", Eqs (8)–(17)), <https://doi.org/10.1371/journal.pcbi.1004731> (PMC4734774).
