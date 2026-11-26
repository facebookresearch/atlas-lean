# Polynomial adaptation time on unimodal and ridge landscapes

**Model.** A population of size $N$ in the weak-mutation regime has genotype $x \in \{0,1\}^n$; each trial mutates a uniformly random site and the mutant fixes with probability $p_{\mathrm{fix}}(\Delta f) = (1 - e^{-2\beta\Delta f})/(1 - e^{-2N\beta\Delta f})$. A fitness function is unimodal if every non-peak genotype has a one-mutation neighbour of strictly higher fitness; let $\delta$ be the smallest such improvement over all genotypes and $d$ the range of fitness values. The ridge landscape $f_{\mathrm{ridge}}(x) = \sum_{i=1}^n\prod_{j\le i} x_j$ counts leading ones: only flipping the first zero improves fitness, all mutations behind it are neutral, and flipping one of the leading ones is deleterious.

**Theorem.**
1. (Unimodal class.) For $N \ge 3$, the drift in fitness satisfies
$$\Delta(x) \ge \delta\,p_{\mathrm{fix}}(\delta)\Big[\frac1n - \Big(1 + \frac1\delta\Big)e^{-2(N-1)\beta\delta}\Big],$$
so if $2(N-1)\beta\delta \ge \ln[(1 + 1/\delta)\,cn]$ for a constant $c > 1$, then $\Delta \ge \gamma\,\delta\,p_{\mathrm{fix}}(\delta)/n$ for a constant $\gamma > 0$ and the expected time to the peak is
$$O\Big(\frac{n}{p_{\mathrm{fix}}(\delta)}\cdot\frac{d}{\delta}\Big).$$
2. (Ridge.) On $f_{\mathrm{ridge}}$ with $N \ge 3$ and $\beta \ge 1/2$,
$$\Delta \ge \frac1n\,p_{\mathrm{fix}}(1)\big[1 - 3e^{-2(N-1)\beta}\big] \ge \frac{6}{8}\cdot\frac{p_{\mathrm{fix}}(1)}{n},$$
and the expected time to reach the peak is $O\big(n^2/p_{\mathrm{fix}}(1)\big)$, for every selection strength above this constant, independent of $n$.

## Depends on

- [Logarithmic selection threshold for adaptation on additive landscapes](logarithmic-selection-threshold-for-adaptation-on-additive-landscapes.md)

## Expansion

In a unimodal landscape a beneficial neighbour of gain at least $\delta$ is hit with probability at least $1/n$, while at most $n-1$ deleterious mutations act against it; bounding their total backward contribution with $p_{\mathrm{fix}}(-\Delta f) = e^{-2(N-1)\beta\Delta f}p_{\mathrm{fix}}(\Delta f)$ gives the drift bound, and the variable drift theorem over fitness values from $\delta$ to $d$ gives the time bound. The bound can be loose (for additive functions $d = n$ gives $O(n^2)$ instead of $O(n\ln n)$) and need not be polynomial when $d/\delta$ is exponential. On the ridge, a deleterious flip of the $j$-th leading one loses the whole suffix but has only probability $p_{\mathrm{fix}}(-(\cdot))$, exponentially small in the loss, so summing over positions costs at most a factor $3e^{-2(N-1)\beta}$; neutral drift on the plateau never hurts. Hence ordered, strongly epistatic adaptation needs only constant selection strength, in contrast with the logarithmic threshold for additive traits.

## Sources

- J. P. Heredia, B. Trubenová, D. Sudholt, T. Paixão, "Selection limits to adaptive walks on correlated landscapes", Genetics 205:803–825 (2017), Eqs (1)–(2) and (6)–(8), the ridge-function analysis with Fig 4, and Appendices B–C (Lemmas 1–3, Theorems 4–7), <https://doi.org/10.1534/genetics.116.189340>, PMCID PMC5289853.
