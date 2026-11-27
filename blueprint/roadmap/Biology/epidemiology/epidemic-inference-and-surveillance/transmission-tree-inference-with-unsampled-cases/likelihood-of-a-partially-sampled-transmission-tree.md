# Likelihood of a partially sampled transmission tree

Let infections follow a branching process in which each case has $k$ offspring with probability
$\alpha(k) = \binom{k+r-1}{k} p^k (1-p)^r$ (negative binomial, $r > 0$, $p \in (0,1)$, mean
$R = rp/(1-p)$, generating function $G(z) = \left(\frac{1-p}{1-pz}\right)^r$), offspring are
infected at times since infection drawn from a generation-time density $\gamma$, and every case is
sampled independently with probability $\pi \in (0,1]$ at a time since infection with density
$\sigma$. The outbreak is finished (observed to extinction). Call a case *included* if it is
sampled or has a sampled descendant, and *excluded* otherwise.

The exclusion probability $\omega_\ast$ is a root in $[0,1]$ of

$$\omega_\ast = (1-\pi)\, G(\omega_\ast).$$

The number of included offspring of a case is $d$ with probability
$\sum_{k \ge d} \binom{k}{d}\alpha(k)\,\omega_\ast^{k-d}(1-\omega_\ast)^d$; define the modified
offspring function

$$\alpha_\ast(d) = \sum_{k=d}^{\infty} \binom{k}{d}\, \alpha(k)\, \omega_\ast^{\,k-d}.$$

For a transmission tree $T$ whose $n$ nodes are the included cases, with sampling indicators
$s_i \in \{0,1\}$, infection times $t_i^{\mathrm{inf}}$, sampling times $t_i^{\mathrm{sam}}$
(when $s_i = 1$) and $d_i$ included offspring indexed by $j$, the probability of $T$ is

$$p_\ast(T \mid \theta) = \prod_{i=1}^{n} \Big[ (1-\pi)^{1-s_i}
\big(\pi\, \sigma(t_i^{\mathrm{sam}} - t_i^{\mathrm{inf}})\big)^{s_i}\,
\alpha_\ast(d_i) \prod_{j=1}^{d_i} \gamma(t_j^{\mathrm{inf}} - t_i^{\mathrm{inf}}) \Big].$$

If sampling is complete ($\pi = 1$) then $\omega_\ast = 0$ and $\alpha_\ast = \alpha$.

## Depends on

- [Negative-binomial offspring distribution](../../superspreading-and-negative-binomial-offspring/nb-offspring.md)
- [Negative-binomial probability generating function](../../superspreading-and-negative-binomial-offspring/nb-pgf.md)

## Expansion

A case is excluded when it is unsampled and each of its offspring is excluded, independently,
which gives the fixed-point equation for $\omega_\ast$ (solved numerically). Conditioning the root
$\rho$ of $T$ on its total offspring number $k$, exactly $d_\rho$ of the $k$ offspring must be
included and the other $k - d_\rho$ excluded, so the root contributes
$\sum_k \binom{k}{d_\rho}\alpha(k)\,\omega_\ast^{k-d_\rho}$ times the subtree probabilities and the
generation-time densities of its included offspring (Eq. 5). The bracketed factors do not depend on
$k$, so the sum collapses to $\alpha_\ast(d_\rho)$ (Eq. 6), and induction over subtrees gives the
product formula (Eq. 7). Each included offspring's own subtree term replaces the factor
$1 - \omega_\ast$ of the included-offspring probability.

## Sources

- X. Didelot, C. Fraser, J. Gardy, C. Colijn, "Genomic infectious disease epidemiology in
  partially sampled and ongoing outbreaks", Molecular Biology and Evolution 34 (2017) 997-1007,
  "Basic Epidemiological Model" and "Finished Outbreak Scenario", Eqs. (2)-(7),
  <https://doi.org/10.1093/molbev/msw275> (PMC5850352).
