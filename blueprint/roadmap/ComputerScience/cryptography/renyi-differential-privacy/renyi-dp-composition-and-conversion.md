# Post-processing, adaptive composition and conversion for Rényi differential privacy

Let $\alpha > 1$. (i) *Post-processing:* if $M$ is $(\alpha, \varepsilon)$-RDP and $K$ is any Markov kernel (randomized map), then $K \circ M$ is $(\alpha, \varepsilon)$-RDP. (ii) *Adaptive sequential composition:* if $M_1$ is $(\alpha, \varepsilon_1)$-RDP and, for every first output $r_1$, $M_2(r_1, \cdot)$ is $(\alpha, \varepsilon_2)$-RDP, then releasing $(r_1, r_2)$ is $(\alpha, \varepsilon_1 + \varepsilon_2)$-RDP; for $k$ adaptive rounds with round-dependent budgets $\varepsilon_i$ the composition is $(\alpha, \sum_i \varepsilon_i)$-RDP. (iii) *Conversion:* if $M$ is $(\alpha, \varepsilon)$-RDP, then for every $0 < \delta < 1$, $M$ is

$$
\Bigl(\varepsilon + \frac{\log(1/\delta)}{\alpha - 1},\; \delta\Bigr)\text{-differentially private}.
$$

## Proof sketch

(i) is the data-processing inequality for Rényi divergence (Jensen applied to the convex function $t \mapsto t^\alpha$). (ii) The Rényi moment of a joint distribution factors conditionally on the first output. (iii) Apply Markov's inequality to the privacy loss: by Hölder, $P(S) \le (e^{D_\alpha} Q(S))^{(\alpha-1)/\alpha}$, and split according to whether $Q(S)$ exceeds the threshold.

## Depends on

- [Rényi divergence and Rényi differential privacy](renyi-differential-privacy.md)
- [Post-processing by a Markov kernel](../differential-privacy/bind.md)

## Proof depends on

- [Differential privacy as a hockey-stick divergence bound](hockey-stick-characterization.md)

## Sources

- Ilya Mironov, "Rényi Differential Privacy", 2017 IEEE 30th Computer Security Foundations Symposium (CSF), 2017.
