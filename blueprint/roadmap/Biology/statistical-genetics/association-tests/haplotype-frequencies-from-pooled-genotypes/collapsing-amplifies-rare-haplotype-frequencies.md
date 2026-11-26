# Collapsing amplifies rare haplotype frequencies and the EM with an internal list

**Setting.** As in the [collapsed-data MLE](collapsed-data-mle-of-haplotype-frequencies.md): pools of $k$ individuals ($K = 2k$ haplotypes), haplotype law $f$ on $\{0,1\}^L$, collapsed-data law $g$.

**Lemma.** For every non-ancestral haplotype $y \ne 0$,

$$g(y) \ge 2k\,f(y)\,f(0)^{2k-1},\qquad\text{so}\qquad g(y) > f(y)\ \text{ whenever }\ f(0) > \Big(\frac{1}{2k}\Big)^{1/(2k-1)} .$$

Meanwhile $g(0) = f(0)^{2k} < f(0)$: pooling and collapsing move probability from the ancestral haplotype to the non-ancestral ones.

**Capture probability.** A haplotype with collapsed probability $g(y)$ appears among $n$ collapsed pool vectors with probability $1-(1-g(y))^n \approx 1 - e^{-n g(y)}$, against $1-(1-f(y))^n$ for $n$ directly sampled haplotypes. To capture $y$ with probability at least $1-\varepsilon$ it suffices (Poisson approximation) that $n \ge -\log(\varepsilon)/g(y)$.

**EM with a list.** If the haplotypes were observed, the MLE would be $\hat f_C(y) = m(y)/(nK)$ with $m(y)$ the count of $y$. EM restricted to a list $R\subset\Omega$ iterates

$$\hat m^{(t)}(y) = \sum_{i=1}^n K\,\mathbb{P}(Y_{i1} = y \mid T_i = t_i),\qquad \mathbb{P}(Y_{i1}=y\mid T_i=t_i) = \frac{\sum_{y_2+\dots+y_K = t_i - y}\hat f^{(t)}(y)\prod_{j\ge 2}\hat f^{(t)}(y_j)}{\sum_{y_1+\dots+y_K = t_i}\prod_{j}\hat f^{(t)}(y_j)},\qquad \hat f^{(t+1)}(y) = \frac{\hat m^{(t)}(y)}{nK},$$

with all sums over haplotypes in $R$. The internal list starts from the distinct collapsed vectors (the CD list), is augmented with every haplotype carrying a single variant, and is trimmed at each iteration of haplotypes whose estimated frequency falls below a threshold; the threshold is benchmarked by matching the EM estimate of $f(0)$ to its collapsed-data MLE.

## Depends on

- [Collapsed-data MLE of haplotype frequencies from pooled genotypes](collapsed-data-mle-of-haplotype-frequencies.md)

## Expansion

One way to obtain $Z = y$ is that exactly one of the $2k$ haplotypes in the pool equals $y$ and the other $2k-1$ are ancestral, which has probability $2k\,f(y)f(0)^{2k-1}$; this lower bound exceeds $f(y)$ under the stated threshold. Not every haplotype can gain, since $f$ and $g$ both sum to one, and $g$ also puts mass on vectors with $f(y) = 0$ (unions of true haplotypes), which is why trimming is needed. In a 25-locus example the haplotype with five variants has $f(y) = 0.0034$ but $g(y) = 0.0097$ at $k = 3$, so 200 pools capture it with probability $1-(1-0.0097)^{200} \approx 0.858$. The E-step is the expensive part because it enumerates all compositions of each pool total; restricting it to a list of 20 to 40 haplotypes, instead of $2^{25}$ or $2^{32}$, makes the pooled-data EM feasible, and the augmented and trimmed list outperformed the collapsed-data MLE and the untrimmed lists in simulation.

## Sources

- Kuk AY, Li X, Xu J, Xu J. An EM algorithm based on an internal list for estimating haplotype distributions of rare variants from pooled genotype data. *BMC Genetics* 14:82 (2013), Methods, Eqs. 2-4 and Lemma 1. <https://doi.org/10.1186/1471-2156-14-82>. PMCID: PMC3847674.
