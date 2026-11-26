# Transferred clonal diversity and intermetastatic $F_{ST}$

Let a primary tumour have clone frequencies $\bar\gamma_1, \dots, \bar\gamma_N$ and seed a metastasis with total influx $k$ and clone influxes $k_i = k\bar\gamma_i$, so that the metastatic clone frequencies are [Dirichlet](dirichlet-clone-frequencies-and-polyclonality-of-metastases.md) with parameters $k\bar\gamma_i$. Measure clonal diversity by the Simpson index, the probability that two random cells are descended from different clones:

$$D_1 = 1 - \sum_{i=1}^{N}\bar\gamma_i^2 \quad\text{(primary)}, \qquad D_2 = 1 - \sum_{i=1}^{N}\gamma_i^2 \quad\text{(metastasis)}.$$

**Transferred diversity.** The expected fraction of the primary tumour's diversity carried into the metastasis is

$$\frac{\mathbb{E}[D_2]}{D_1} = \frac{k}{1+k} = \frac{\lambda}{b+\lambda},$$

where $\lambda = bk$ is the total seeding rate and $b$ the division rate. A metastasis seeded once ($k \to 0$) inherits none of the primary diversity, and one seeded many cells per generation ($k \gg 1$) inherits nearly all of it.

**Differentiation between metastases.** If the primary tumour seeds $M$ metastases independently with equal influx $k$, the fixation index $F_{ST} = 1 - \mathbb{E}[D_2]/D_2^*$, with $D_2^*$ the diversity of the pooled metastatic cells, tends as $M \to \infty$ to

$$F_{ST} \to \frac{1}{1+k}.$$

**Inference.** Given clone frequencies $\gamma_{ij}$ of clone $i$ in tumour $j$, the maximum-likelihood total influx $\hat k_j$ to tumour $j$ is, to first order,

$$\hat k_j \approx \frac{N-1}{\alpha\, D_{\mathrm{KL}}(\bar\gamma \,\|\, \gamma_{\cdot j})}, \qquad D_{\mathrm{KL}}(\bar\gamma\,\|\,\gamma_{\cdot j}) = \sum_{i}\bar\gamma_i \ln\frac{\bar\gamma_i}{\gamma_{ij}},$$

with $\alpha$ between $1$ (large divergence) and $2$ (small divergence), and $\ln \hat k_j$ has variance about $\alpha/(N-1)$. The expected number of seeding cells that founded surviving lineages before the metastasis reached size $Y$ is $k\bigl(\ln(\rho Y) - \psi(k)\bigr)$, with $\rho$ the lineage survival probability and $\psi$ the digamma function.

## Depends on

- [Dirichlet clone frequencies and polyclonality of metastases](dirichlet-clone-frequencies-and-polyclonality-of-metastases.md)
- [Wright's hierarchical F-statistics identity](../../population-structure/wright-s-f-statistics/hierarchical-f-statistics.md)

## Proof sketch

With $\operatorname{Var}(\gamma_i) = \bar\gamma_i(1-\bar\gamma_i)/(1+k)$ and $\mathbb{E}\gamma_i = \bar\gamma_i$,

$$\mathbb{E}\sum_i \gamma_i^2 = \sum_i \bar\gamma_i^2 + \frac{1 - \sum_i\bar\gamma_i^2}{1+k},$$

so $\mathbb{E}[D_2] = D_1\bigl(1 - \tfrac{1}{1+k}\bigr) = D_1\,\tfrac{k}{1+k}$. Pooling $M$ independent metastases averages their frequency vectors, which divides the variance term by $M$; as $M \to \infty$ the pooled diversity returns to $D_1$ and $F_{ST} \to 1 - k/(1+k) = 1/(1+k)$. The digamma term comes from the detection time: the total size grows like $e^{rt}\,G/\rho$ with $G$ approximately Gamma-distributed with shape $k$, so $\mathbb{E}[rT] = \ln(\rho Y) - \psi(k)$, and seeding cells that found surviving lineages arrive at rate $\rho\lambda = kr$.

## Sources

- A. Heyde, J. G. Reiter, K. Naxerova and M. A. Nowak, "Consecutive seeding and transfer of genetic diversity in metastasis", Proceedings of the National Academy of Sciences of the USA (2019), Results, Eqs. [7]–[10], and SI Appendix, <https://doi.org/10.1073/pnas.1819408116>, PMCID PMC6628640.
