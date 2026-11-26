# Malignant transit time heterogeneity and non-monotone oxygen metabolism

In the setting of [maximal oxygen extraction under gamma-distributed capillary transit times](maximal-oxygen-extraction-under-gamma-distributed-capillary-transit-times.md), with Crone–Renkin extraction $Q(\tau) = 1 - e^{-k\tau}$, let the arterial oxygen concentration $C_A > 0$ and the capillary blood volume $V > 0$ be fixed. By the central volume theorem, blood flow is $F = V/\mu$, so the maximal metabolic rate of oxygen that the blood can support is

$$\mathrm{CMRO}_{2,\max}(\mu, \sigma) \;=\; C_A\, F\, \mathrm{OEF}_{\max} \;=\; \frac{C_A V}{\mu}\Bigl[1 - \Bigl(1 + \frac{k\sigma^2}{\mu}\Bigr)^{-\mu^2/\sigma^2}\Bigr].$$

1. Homogeneous transit ($\sigma = 0$): $\mathrm{CMRO}_{2,\max} = C_A V (1 - e^{-k\mu})/\mu$ is strictly decreasing in $\mu$, hence strictly increasing in flow, and bounded above by $C_A V k$.
2. Heterogeneous transit ($\sigma > 0$ fixed): $\mathrm{CMRO}_{2,\max}(\mu, \sigma) \to 0$ both as $\mu \to \infty$ (no flow) and as $\mu \to 0^+$ (unbounded flow). It is therefore not monotone in flow: it attains a maximum at some finite flow, and there are flows $F_1 < F_2$ with $\mathrm{CMRO}_{2,\max}$ lower at $F_2$.

Thus, when heterogeneity is not reduced along with mean transit time, raising flow beyond some point lowers the oxygen supply that the tissue can extract, a regime called malignant capillary transit time heterogeneity.

## Depends on

- [Maximal oxygen extraction under gamma-distributed capillary transit times](maximal-oxygen-extraction-under-gamma-distributed-capillary-transit-times.md)

## Expansion

For item 1, $x \mapsto (1 - e^{-x})/x$ is strictly decreasing on $(0, \infty)$ with limit $1$ at $0$, and substituting $x = k\mu$ gives both claims. For item 2 as $\mu \to \infty$, the bracket is at most $1$ and the prefactor $1/\mu$ vanishes. As $\mu \to 0^+$, write $a = \mu^2/\sigma^2 \to 0$ and $y = k\sigma^2/\mu \to \infty$. Then $a\log(1 + y) \to 0$, so $1 - (1 + y)^{-a} = a\log(1 + y)\,(1 + o(1))$ and

$$\mathrm{CMRO}_{2,\max} \;\sim\; C_A V\, \frac{\mu}{\sigma^2}\, \log\Bigl(1 + \frac{k\sigma^2}{\mu}\Bigr) \;\to\; 0 .$$

A positive continuous function on $(0, \infty)$ with zero limits at both ends has an interior maximum and is not monotone. Physiologically, flow increases that shorten mean transit time without homogenizing capillary flow shunt oxygen-rich blood through fast paths. Pericyte-mediated homogenization therefore matters for the oxygen supply, and pathological heterogeneity can produce hypoxia even when flow is normal or raised. The same qualitative behaviour appears when capillary volume grows with flow according to Grubb's relation.

## Sources

- S. N. Jespersen, L. Østergaard, "The roles of cerebral blood flow, capillary transit time heterogeneity, and oxygen tension in brain oxygenation and metabolism", *Journal of Cerebral Blood Flow & Metabolism* 32(2) (2012) 264–277, Materials and methods, "Choice of Blood Volume Term for Maximum Cerebral Metabolic Rate of Oxygen Calculations", and Results, "The parallel arrangement of capillaries allows maximum cerebral metabolic rate of oxygen to decrease with cerebral blood flow" and "Malignant capillary transit time heterogeneity", <https://doi.org/10.1038/jcbfm.2011.153> (PMC3272609).
