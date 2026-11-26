# Logarithmic drift of genome size under duplications and deletions

**Single-mutation chain.** Genome size $s \in \mathbb N$ changes by one of four mutation types:
- small insertion: $+1, \dots, +l_{\mathrm{ins}}$ bases, with a law not depending on $s$;
- small deletion: $-1, \dots, -l_{\mathrm{sdel}}$ bases (truncated at $0$), law not depending on $s$;
- duplication: new size uniform on $\{s+1, \dots, 2s\}$;
- large deletion: new size uniform on $\{0, \dots, s-1\}$,

with $l_{\mathrm{ins}}, l_{\mathrm{sdel}} < \infty$. Let $S_n$ be the size after $n$ mutations and

$$\Delta(s) = \mathbb E[\log S_{n+1} \mid S_n = s] - \log s .$$

with the convention $\log 0 := 0$, so that a large deletion reaching size $0$ (probability $1/s$) contributes a finite term.

**Property 1.** As $s \to \infty$, conditional on the type of the next mutation,

$$\Delta(s) \to -1 \ \text{(large deletion)}, \qquad \Delta(s) \to 2\log 2 - 1 \ \text{(duplication)}, \qquad \Delta(s) \to 0 \ \text{(small indel)}.$$

**Lemma 2 (shrinking of large genomes).** If mutations of each type occur at per-base rates $\mu_{\mathrm{ins}}, \mu_{\mathrm{sdel}}, \mu_{\mathrm{dup}}, \mu_{\mathrm{ldel}}$ and

$$(2\log 2 - 1)\,\mu_{\mathrm{dup}} < \mu_{\mathrm{ldel}},$$

there are $\delta > 0$, $\varepsilon' > 0$ and a threshold $\tilde s$ with $\mathbb E[\log S_{n+1} \mid S_n = s] \le \log s - \delta$ for all $s \ge \tilde s$ (again with $\log 0 := 0$), and for every initial size $s_0$ and every $n \ge 0$

$$\Pr_{s_0}\bigl(S_n \le \tilde s\bigr) \ge \begin{cases} \varepsilon' & \text{if } s_0 \le \tilde s, \\ \varepsilon'\Bigl(1 - \dfrac{\log s_0}{\log \tilde s + n\delta}\Bigr) & \text{if } s_0 > \tilde s. \end{cases}$$

Note that the condition holds even when duplications are up to $1/(2\log 2 - 1) \approx 2.59$ times as frequent as large deletions, and regardless of the indel rates.

## Expansion

For a duplication from size $s$, $\log(S_{n+1}/s)$ is a Riemann sum of $\log x$ over $x \in (1, 2]$, so its mean tends to $\int_1^2 \log x\,dx = 2\log 2 - 1 \approx 0.386$; for a large deletion, with $\log 0 := 0$ for the outcome $0$, it tends to $\int_0^1 \log x\, dx = -1$; a bounded indel changes $\log s$ by $O(1/s)$. Although at fixed $s$ the mean gain of a duplication ($\approx s/2$ bases) equals the mean loss of a large deletion, on the multiplicative scale on which these events act, a deletion followed by a duplication loses on average, so equal rates produce a net downward drift. Weighting the limits by the type probabilities, proportional to the per-base rates, gives the drift $(\mu_{\mathrm{dup}}(2\log 2 - 1) - \mu_{\mathrm{ldel}})/\mu$, negative under the stated condition; a supermartingale and return-time argument converts the drift into the hitting bound.

## Sources

- S. Fischer, S. Bernard, G. Beslon, C. Knibbe, "A model for genome size evolution", Bulletin of Mathematical Biology 76(9) (2014) 2249-2291, sections "Definition of the Model" and "Fundamental Properties of the Gain and Loss Distributions", Property 1 and Lemma 2, with proofs in Appendix 1, <https://doi.org/10.1007/s11538-014-9997-8>, PMCID PMC4153982.
