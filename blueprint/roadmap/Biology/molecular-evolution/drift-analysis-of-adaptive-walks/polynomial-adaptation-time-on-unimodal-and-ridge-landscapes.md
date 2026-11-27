# Polynomial adaptation time on unimodal and ridge landscapes

**Model.** A population of size $N$ in the weak-mutation regime has genotype $x \in \{0,1\}^n$; each trial mutates a uniformly random site and the mutant fixes with probability $p_{\mathrm{fix}}(\Delta f) = (1 - e^{-2\beta\Delta f})/(1 - e^{-2N\beta\Delta f})$. A fitness function is unimodal if every non-peak genotype has a one-mutation neighbour of strictly higher fitness; let $\delta$ and $d$ be the smallest and the largest fitness difference between any two genotypes (increases or decreases alike). The ridge landscape $f_{\mathrm{ridge}}(x) = \sum_{i=1}^n\prod_{j\le i} x_j$ counts leading ones: only flipping the first zero improves fitness, all mutations behind it are neutral, and flipping one of the leading ones is deleterious.

**Theorem.**
1. (Unimodal class.) For $N \ge 3$ and $\beta \ge 1/2$, the drift in fitness satisfies

$$\Delta(x) \ge \delta\,p_{\mathrm{fix}}(\delta)\Big[\frac1n - \Big(1 + \frac1\delta\Big)e^{-2(N-1)\beta\delta}\Big],$$

so if $2(N-1)\beta\delta \ge \ln[(1 + 1/\delta)\,cn]$ for a constant $c > 1$, then $\Delta \ge \gamma\,\delta\,p_{\mathrm{fix}}(\delta)/n$ for a constant $\gamma > 0$ and the expected time to the peak is

$$O\Big(\frac{n}{p_{\mathrm{fix}}(\delta)}\cdot\frac{d}{\delta}\Big).$$

2. (Ridge.) On $f_{\mathrm{ridge}}$ with $N \ge 3$ and $\beta \ge 1/2$,

$$\Delta \ge \frac1n\,p_{\mathrm{fix}}(1)\big[1 - 3e^{-2(N-1)\beta}\big] \ge \big(1 - 3e^{-2}\big)\frac{p_{\mathrm{fix}}(1)}{n},$$

since $2(N-1)\beta \ge 2$, with $1 - 3e^{-2} \approx 0.59 > 0$; the expected time to reach the peak is therefore $O\big(n^2/p_{\mathrm{fix}}(1)\big)$, for every selection strength above this constant, independent of $n$.

## Depends on

- [Closed form of Kimura's fixation probability](../../population-genetics/moran-model/kimura-fixation-half.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Related topics

- [Logarithmic selection threshold for adaptation on additive landscapes](logarithmic-selection-threshold-for-adaptation-on-additive-landscapes.md): the additive case, which needs selection strength growing logarithmically in the number of sites.

## Expansion

In a unimodal landscape a beneficial neighbour of gain at least $\delta$ is hit with probability at least $1/n$, while at most $n-1$ deleterious mutations act against it; bounding their total backward contribution with $p_{\mathrm{fix}}(-\Delta f) = e^{-2(N-1)\beta\Delta f}p_{\mathrm{fix}}(\Delta f)$ gives the drift bound. That step needs both hypotheses: because every fitness loss is at least $\delta$ and $\beta \ge 1/2$, the source bounds the backward contribution of each deleterious step by $(1+\delta)\,p_{\mathrm{fix}}(-\delta)$, which produces the factor $1 + 1/\delta$. The variable drift theorem over fitness values from $\delta$ to $d$ gives the time bound. The bound can be loose (for additive functions $d = n$ gives $O(n^2)$ instead of $O(n\ln n)$) and need not be polynomial when $d/\delta$ is exponential. On the ridge, a deleterious flip of the $j$-th leading one loses the whole suffix but has only probability $p_{\mathrm{fix}}(-(\cdot))$, exponentially small in the loss, so summing over positions costs at most a factor $3e^{-2(N-1)\beta}$; neutral drift on the plateau never hurts. Hence ordered, strongly epistatic adaptation needs only constant selection strength, in contrast with the logarithmic threshold for additive traits. The source states the constant of the ridge drift bound as $6/8$, which fails at $N = 3$, $\beta = 1/2$, where $1 - 3e^{-2} \approx 0.59 < 6/8$; the time bound $O(n^2/p_{\mathrm{fix}}(1))$ is unaffected.

## Sources

- J. P. Heredia, B. Trubenová, D. Sudholt, T. Paixão, "Selection limits to adaptive walks on correlated landscapes", Genetics 205:803–825 (2017), Eqs (1)–(2) and (6)–(8), the ridge-function analysis with Fig 4, Appendix B (Lemmas 2–3) and Appendix F (Theorems 12–13), <https://doi.org/10.1534/genetics.116.189340>, PMCID PMC5289853.
