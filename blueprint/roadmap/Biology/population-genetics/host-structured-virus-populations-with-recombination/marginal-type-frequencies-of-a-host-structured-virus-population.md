# Marginal type frequencies of a host-structured virus population

**Model.** There are $M = M_N$ hosts, each carrying exactly $N$ virions, and each virion has a sequence type in $[K]^L$ ($L$ loci with $K$ alleles each). The state $x = (x_{m,n,\ell})$ evolves as a continuous-time Markov chain with per-host event rates:

- *replication* at total rate $N\gamma_N$: in host $m$ virion $n_1$ produces an offspring that replaces virion $n_2$ (a Moran step);
- *reinfection* at rate $\lambda_N$: a virion copied from a uniformly chosen host replaces a uniformly chosen virion of host $m$;
- *host replacement* at rate $1$: all virions of host $m$ are replaced by copies of a single virion drawn from a uniformly chosen host;
- *parent-independent mutation* at rate $\mu_N$: a virion is replaced by type $\mathbf k \sim \nu$, where $\nu$ is a probability measure on $[K]^L$;
- *recombination* at rate $\rho_N$: a virion is replaced by a recombinant that takes the loci in $\mathbf r \in \mathcal R$ from one parent and the remaining loci from another parent in the same host, $\mathbf r$ chosen with probability $p_{\mathbf r} > 0$.

**Assumptions.** (A1) For all loci $\ell_1 \neq \ell_2$ some $\mathbf r \in \mathcal R$ separates them, $|\{\ell_1,\ell_2\} \cap \mathbf r| = 1$. (A2) As $N \to \infty$: $\lambda_N/\gamma_N \to \theta > 0$; $N, \mu_N, \rho_N \in o(\gamma_N)$; $\mu_N \in o(\rho_N)$; and either $\lambda_N/(M\mu_N) \to 0$ (case i) or $\lambda_N/(M\mu_N) \to C > 0$ (case ii). (A3) Every marginal $\nu_\ell$ of $\nu$ has full support on $[K]$.

**Stationarity.** Under (A1) and (A3) with $\mu_N > 0$ the chain has a unique stationary distribution, with full support for $N$ large; let $\mathbf X^N$ denote the stationary process.

**Theorem (locus-wise frequencies).** Let $\bar X^N_\ell(T) = \frac{1}{MN}\sum_{m,n}\delta_{X^N_{m,n,\ell}(T)} \in \mathcal M_1([K])$ and $\bar X^N(T) = (\bar X^N_1(T), \dots, \bar X^N_L(T))$. Under (A1) to (A3), $\bar X^N(T) \Rightarrow \bar X$ as $N \to \infty$, where

- in case (i), $\bar X = (\nu_\ell)_{\ell \in [L]}$ is deterministic;
- in case (ii), the components $\bar X_\ell$ are independent and $\bar X_\ell \sim \mathrm{Dir}\big(\tfrac{1+\theta}{C}\nu_\ell\big)$.

In case (ii) the limit is the stationary law of $L$ independent $K$-type Wright-Fisher diffusions with parent-independent mutation, with mutation coefficient $\frac12\frac{C}{1+\theta}\nu_\ell(\{k\})$ toward type $k$ at locus $\ell$.

## Depends on

- [The Dirichlet law is stationary for parent-independent mutation](../diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)

## Expansion

Fast replication and reinfection make each host a well-mixed Moran population that is constantly reseeded from the whole population, so on the slow time scale the population-wide frequency at each locus behaves like a single Wright-Fisher population whose effective drift comes from host replacement and reinfection, while mutation enters at rate $\mu_N$ per virion. The ratio $\lambda_N/(M\mu_N)$ compares the strength of between-host genetic drift with mutation: if mutation dominates (case i), frequencies are pinned at the mutation law; if they balance (case ii), a Dirichlet stationary law appears. Recombination faster than mutation and assumption (A1) decouple the loci, which explains the independence across $\ell$. The proof traces the genealogy of a sample backward in time.

## Sources

- R. Eichhorn and C. Pokalyuk, "On a Neutral Host-Virus Model with Recombination", arXiv preprint (2025), Assumption 2.1, Assumptions 2.3, Assumption 2.4, Proposition 2.5 and Theorem 2.9. <https://doi.org/10.48550/arXiv.2509.19253>