# Conservative bias of Storey's null proportion estimator

Let $\mu$ be a probability measure on $\Omega$, $p_1, \dots, p_m : \Omega \to \mathbb{R}$ measurable and $H_0 \subseteq \{1, \dots, m\}$ a fixed set of true nulls whose p-values are valid under $\mu$ ($\mu(p_i \le u) \le u$ for $u \in [0, 1]$). For every $t \in [0, 1)$,

$$\frac{|H_0|}{m} \le \mathbb{E}_\mu\big[\hat\pi_0(t)\big],$$

where $\hat\pi_0$ is [Storey's estimator](storey-pi0.md). No independence is assumed; the non-null p-values are arbitrary measurable functions.

## Sources

- J. D. Storey, *A direct approach to false discovery rates*, J. R. Stat. Soc. B 64 (2002), 479–498.
