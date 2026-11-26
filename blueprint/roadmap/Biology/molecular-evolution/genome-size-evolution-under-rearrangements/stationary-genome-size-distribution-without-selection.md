# Stationary genome size distribution without selection

**Generational chain.** In each generation a genome of size $s$ undergoes a Poisson$(\mu s)$ number of mutations, $\mu = \mu_{\mathrm{ins}} + \mu_{\mathrm{sdel}} + \mu_{\mathrm{dup}} + \mu_{\mathrm{ldel}}$, each of type chosen in proportion to its rate and acting as in the single-mutation chain (small indels of bounded length, duplications and large deletions of size uniform between $1$ and the current size). Sizes ending at $0$ are reassigned to $1$, giving a transition matrix $M_G$ on $\mathbb N^\ast = \{1, 2, \dots\}$. Without selection the population size distribution evolves as $\nu_{t+1} = \nu_t M_G$.

**Theorem 1 (Doeblin's condition in $g$ steps).** If a stochastic matrix $M$ on a countable space $S$ satisfies $(M^g)_{i\, i_f} \ge \varepsilon$ for all $i \in S$, for some $g \ge 1$, state $i_f$ and $\varepsilon > 0$, then $M$ has a unique stationary distribution $\pi$, and for every initial distribution $\mu$
$$\|\mu M^t - \pi\|_1 \le 2(1 - \varepsilon)^{\lfloor t/g \rfloor}, \qquad t \ge 0 .$$

**Theorem 2.** If $(2\log 2 - 1)\,\mu_{\mathrm{dup}} < \mu_{\mathrm{ldel}}$, then $M_G$ has a unique stationary distribution $\nu_\infty$ and $\lim_{t \to \infty} \|\nu_0 M_G^t - \nu_\infty\|_1 = 0$ for every initial distribution $\nu_0$. Genome size therefore stays bounded in distribution, whatever the rates of small insertions such as transposable element activity.

**Corollary 1 (general rearrangement laws).** The same conclusion holds for other size distributions of duplications and deletions, provided that after a suitable scaling $f$ of genome size the asymptotic mean jump of duplications times $\mu_{\mathrm{dup}}$ is strictly smaller than the asymptotic mean loss of deletions times $\mu_{\mathrm{ldel}}$; for uniform laws $f = \log$.

## Depends on

- [Logarithmic drift of genome size under duplications and deletions](logarithmic-drift-of-genome-size-under-duplications-and-deletions.md)

## Expansion

All states of $M_G$ communicate in one generation because each size can gain or lose exactly one base by some mutation, but $\mathbb N^\ast$ is infinite, so transition probabilities into a fixed state are not automatically bounded below. Split the space at the threshold $\tilde s$ of the drift lemma. From a finite set of small sizes, a fixed target $s_f \le \tilde s$ is reached in one generation with probability at least $\varepsilon_1 > 0$ (Lemma 1). From a large size, the number of mutations in one generation is of order $\mu s$, enough (by Chebyshev's inequality) for the negative logarithmic drift to bring the genome below $\tilde s$ with probability bounded away from $0$. Combining both steps verifies Doeblin's condition with $g = 2$, and Theorem 1 gives existence, uniqueness and geometric convergence. Bounds on the quantiles of $\nu_\infty$ follow from Cantelli's inequality (Lemma 3, Proposition 1).

## Sources

- S. Fischer, S. Bernard, G. Beslon, C. Knibbe, "A model for genome size evolution", Bulletin of Mathematical Biology 76(9) (2014) 2249-2291, Theorems 1-2, Lemmas 1-3, Proposition 1 and Corollary 1, <https://doi.org/10.1007/s11538-014-9997-8>, PMCID PMC4153982.
