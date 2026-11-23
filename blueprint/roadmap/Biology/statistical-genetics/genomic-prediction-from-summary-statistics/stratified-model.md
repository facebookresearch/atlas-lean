# Stratified LD-score model

Let $\mu$ be a measure on a measurable space $\Omega$, let $N$ and $M$ be natural numbers (individuals and markers), and let $\mathcal{C}$ be a finite set of annotation categories. A stratified LD-score model consists of

- for each category $c \in \mathcal{C}$, a set of markers $C_c \subseteq \{1, \dots, M\}$ (the sets may overlap) and a real number $\tau_c$ (its per-marker contribution to heritability);
- a real number $\sigma_e^2$ (the noise second moment);
- real functions $\beta_1, \dots, \beta_M$ (effects) and $\varepsilon_1, \dots, \varepsilon_N$ (noise) on $\Omega$, square integrable with respect to $\mu$,

such that for all markers $k, l$ and individuals $i, i'$

- $\int \beta_k \beta_l \, d\mu = \sum_{c \,:\, k \in C_c} \tau_c$ if $k = l$, and $0$ otherwise;
- $\int \varepsilon_i \varepsilon_{i'} \, d\mu = \sigma_e^2$ if $i = i'$, and $0$ otherwise;
- $\int \beta_k \varepsilon_i \, d\mu = 0$.

In general the moment conditions are raw second moments; they are variances and covariances when $\mu$ is a probability measure and the effects and noise are centred. The model of Finucane et al. (2015) also normalizes the phenotypic variance so that $\sigma_e^2 \approx 1$ and has a confounding term, which is not part of this model.

## Sources

- H. K. Finucane et al., *Partitioning heritability by functional annotation using genome-wide association summary statistics*, Nat. Genet. 47 (2015), 1228–1235.
