# Lineage trajectories under mutation–selection balance at a non-recombining locus

Consider a haploid asexual population (or a perfectly linked locus in a semidominant diploid) in which deleterious mutations arise at rate $U_d$ per individual per generation, each reducing log fitness by $s > 0$ with no epistasis, so an individual with $k$ mutations has log fitness $-ks$. Write $\lambda = U_d / s$. When selection is strong enough that deleterious alleles do not fix, the population sits at the steady state of Kimura–Maruyama and Haigh, in which the fraction of individuals carrying $k$ mutations is

$$h_k = e^{-\lambda} \frac{\lambda^k}{k!}, \qquad k = 0, 1, 2, \dots,$$

with mean number $\bar k = \lambda$.

Label a new neutral mutation that arises at time $0$ in $n_k(0)$ individuals all carrying $k$ deleterious mutations, and let $n_{k+j}(t)$ be the number of its carriers with $k + j$ mutations. Ignoring genetic drift (the deterministic limit of the Langevin dynamics, with the population mean held at $\bar k = \lambda$),

$$\frac{d n_{k+j}}{dt} = -(k+j)s\, n_{k+j} + \lambda s\, n_{k+j} - U_d\, n_{k+j} + U_d\, n_{k+j-1}, \qquad n_{k-1} \equiv 0.$$

**Proposition.** The solution with $n_{k+j}(0) = n_k(0)\,\mathbf 1[j = 0]$ is

$$n_{k+j}(t) = n_k(0)\, e^{-kst}\, \frac{\mu(t)^j}{j!}, \qquad \mu(t) = \lambda\left(1 - e^{-st}\right),$$

so the number of mutations the lineage has gained by time $t$ is $\mathrm{Poisson}(\mu(t))$. Consequently:

1. the mean relative fitness of the lineage is $x(t) = U_d e^{-st} - ks$;
2. the lineage size is $n(t) = n_k(0)\, g_k(t)$ with

$$g_k(t) = \exp\!\left(-kst + \lambda\left(1 - e^{-st}\right)\right);$$

3. a lineage founded in the mutation-free class ($k = 0$) grows monotonically to $n_0(0)\, e^{\lambda}$, reaching its own mutation–selection balance after about $t_d = (\ln \lambda)/s$ generations;
4. a lineage founded in class $1 \le k < \lambda$ grows only until

$$t_d(k) = \frac{\ln(\lambda / k)}{s},$$

where it peaks at $n_k(0)\, \tilde g_k$ with $\tilde g_k = g_k(t_d(k)) = e^{\lambda} \left(\dfrac{k}{e\lambda}\right)^{k}$, stays within a constant factor of the peak for a time of order $\Delta t(k) = 1/(s\sqrt{k})$, and then declines at rate $ks$; a lineage founded in class $k \ge \lambda$ declines from the start.

In particular the founding genotype itself always feels selection $-ks$: a lineage that increases does so by spawning less fit descendants, so it loses fitness while it grows.

## Proof sketch

Substituting $n_{k+j} = A(t)\, \mu(t)^j / j!$ and using $\lambda s = U_d$, the $\lambda s$ and $-U_d$ terms cancel and matching coefficients of $\mu^j/j!$ and $\mu^{j-1}/(j-1)!$ gives $A' = -ks A$ and $\mu' = U_d - s\mu$ with $\mu(0) = 0$, whose solutions are $A = n_k(0) e^{-kst}$ and $\mu = \lambda(1 - e^{-st})$. Summing over $j$ gives $n(t) = A e^{\mu}$, i.e. item 2, and $\frac{d}{dt} \ln g_k = U_d e^{-st} - ks = x(t)$ is item 1. For $k \ge 1$ the derivative vanishes when $e^{-st} = k/\lambda$, giving $t_d(k)$, and substituting gives $\tilde g_k = (k/\lambda)^k e^{\lambda - k}$. Near the peak $\ln g_k$ has second derivative $-s U_d e^{-st_d(k)} = -ks^2$, so $\ln g_k(t_d(k)) - \ln g_k(t) \approx ks^2 (t - t_d(k))^2/2$ and it stays within $O(1)$ of its maximum for a time of order $1/(s\sqrt{k})$. The Poisson description of the added load is due to Etheridge, Pfaffelhuber and Wakolbinger (2009); these deterministic trajectories, combined with drift in the most-fit class, drive the site frequency spectrum of linked neutral sites.

## Depends on

- [Poisson equilibrium of multiplicative mutation–selection balance](../multilocus-multiplicative-mutation-selection-poi.md)

## Sources

- I. Cvijović, B. H. Good and M. M. Desai, "The effect of strong purifying selection on genetic diversity", Genetics 209 (2018), 1235–1278, Model and Results and "Key features of lineage trajectories" (Equations 8, 10–15), <https://doi.org/10.1534/genetics.118.301058> (PMC6063222). Equation 15, $\Delta t(k) = 1/(\sqrt{k}\, s)$, is cited from the journal version; the PMC rendering drops its square root.
