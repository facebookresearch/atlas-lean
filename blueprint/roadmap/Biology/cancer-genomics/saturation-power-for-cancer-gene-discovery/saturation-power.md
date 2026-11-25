# Saturation power of the binomial gene discovery test

For a natural number $N$ (patients) and reals $p_0, p_1, \gamma$, the saturation power is

$$\mathrm{Pow}(N) = \sum_{x \in \{0, \dots, N\} \,:\, P_{p_0}(x) \le \gamma} B(x \mid N, p_1),$$

where $B(x \mid N, p) = \binom{N}{x} p^x (1 - p)^{N - x}$ and $P_{p_0}(x) = \sum_{i=x}^{N} B(i \mid N, p_0)$ is the background upper tail. For $0 \le p_0, p_1 \le 1$ it is the probability, when each patient is mutated independently with probability $p_1$, of a count whose background p-value is at most $\gamma$ (Lawrence et al. 2014).

## Sources

- M. S. Lawrence et al., *Discovery and saturation analysis of cancer genes across 21 tumour types*, Nature 505 (2014), 495–501 (Methods, "Power calculations").
