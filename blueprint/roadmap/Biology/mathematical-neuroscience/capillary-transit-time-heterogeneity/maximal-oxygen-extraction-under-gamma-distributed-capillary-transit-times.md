# Maximal oxygen extraction under gamma-distributed capillary transit times

Let $Q : [0, \infty) \to [0, 1]$ be the oxygen extraction fraction of a single capillary as a function of its transit time $\tau$, and let capillary transit times in a tissue have density $h$ with mean $\mu$ and standard deviation $\sigma$ (the capillary transit time heterogeneity). The maximal oxygen extraction fraction of the bed (zero tissue oxygen tension) is

$$\mathrm{OEF}_{\max} \;=\; \int_0^\infty h(\tau)\, Q(\tau)\, d\tau .$$

1. If $Q$ is concave, then $\mathrm{OEF}_{\max} \le Q(\mu)$, with equality when all transit times equal $\mu$ ($\sigma = 0$).
2. Under the Crone–Renkin single-capillary model, $Q(\tau) = 1 - e^{-k\tau}$ with rate constant $k > 0$, and gamma-distributed transit times with shape $\alpha$ and scale $\beta$ (so $\mu = \alpha\beta$ and $\sigma^2 = \alpha\beta^2$),

$$\mathrm{OEF}_{\max} \;=\; 1 - (1 + k\beta)^{-\alpha} \;=\; 1 - \Bigl(1 + \frac{k\sigma^2}{\mu}\Bigr)^{-\mu^2/\sigma^2}.$$

3. In case 2, for fixed $\mu$, $\mathrm{OEF}_{\max}$ is strictly decreasing in $\sigma > 0$ and tends to $1 - e^{-k\mu}$ as $\sigma \to 0$.

## Depends on

- [Renkin–Crone extraction with plasma protein binding](../../pharmacokinetics/blood-brain-barrier-transport-kinetics/renkin-crone-extraction-with-plasma-protein-binding.md)

## Proof depends on

- [Moment generating function of the gamma distribution](../../../Probability/distributions/continuous/gamma-distribution/gamma-mgf/mgf-gamma-measure-of-lt.md)

## Expansion

Item 1 is Jensen's inequality, $\mathbb{E}\,Q(\tau) \le Q(\mathbb{E}\tau)$ for concave $Q$: splitting flow between fast and slow paths loses more extraction on the fast path than it gains on the slow one. Item 2 uses the gamma Laplace transform $\int h(\tau)e^{-k\tau}d\tau = (1 + k\beta)^{-\alpha}$, with $\alpha = \mu^2/\sigma^2$ and $\beta = \sigma^2/\mu$. For item 3, put $x = k\mu > 0$, so that $(1 + k\beta)^{-\alpha} = (1 + x/\alpha)^{-\alpha}$; the function $\alpha \mapsto (1 + x/\alpha)^{\alpha}$ is strictly increasing with limit $e^x$, and $\alpha$ decreases as $\sigma$ increases. The full model replaces Crone–Renkin by a steady-state capillary equation that includes haemoglobin binding and nonzero tissue oxygen tension; $Q$ then still depends only on $k\tau$, and $k = 118\ \mathrm{s}^{-1}$ was calibrated to a resting $\mathrm{OEF}_{\max}$ of $0.3$ in rat cortex. The predicted extraction varies greatly at fixed blood flow and volume, depending on $\sigma$, which makes capillary flow homogenization a mechanism for raising oxygen extraction during activation without additional flow.

## Sources

- S. N. Jespersen, L. Østergaard, "The roles of cerebral blood flow, capillary transit time heterogeneity, and oxygen tension in brain oxygenation and metabolism", *Journal of Cerebral Blood Flow & Metabolism* 32(2) (2012) 264–277, Materials and methods, "Modeling Oxygen Extraction Capacity as a Function of Tissue Oxygen Tension and Capillary Transit Time Characteristics in Steady State", and Results, "Nonnegligible capillary transit time heterogeneity reduces maximum oxygen extraction fraction relative to single transit time kinetics", <https://doi.org/10.1038/jcbfm.2011.153> (PMC3272609).
