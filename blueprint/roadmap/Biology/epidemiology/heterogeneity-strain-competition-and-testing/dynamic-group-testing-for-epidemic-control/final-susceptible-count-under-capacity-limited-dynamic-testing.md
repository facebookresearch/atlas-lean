# Final susceptible count under capacity-limited dynamic testing of a discrete SIR spread

**Model.** A population of $n$ individuals evolves in discrete time $t = 0, 1, 2, \dots$; each individual is susceptible ($U_i = 0$), infected ($U_i = 1$) or detected and isolated ($U_i = 2$, permanently). At $t = 0$ each individual is infected independently with probability $p$. At each step $t \ge 1$:

- *spread:* each non-isolated infected individual infects each susceptible one independently with probability $q$;
- *testing:* at most $T$ tests are run (individual or pooled; a pooled test is positive iff it contains an infected individual) and every detected infected individual is isolated before the next spread phase.

Let $\alpha(t)$, $\lambda(t)$ and $\gamma(t)$ be the numbers of susceptible, infected non-isolated and isolated individuals at time $t$, and $p'(t)$ the probability that an infected individual escapes detection at time $t$; as a standing assumption, $p'(t)$ depends only on $T$, $\alpha(t)$, $\lambda(t)$ and $\gamma(t)$. A testing policy is *symmetric* if the marginal state law is the same for all individuals and *converging* if $\mathbb{P}(U_i(t) = 1) = o(1/n)$ as $t \to \infty$. The source also assumes $q = o(1/n)$ throughout, which it uses for the linear approximation $(1-q)^x \approx 1 - qx$.

The relations below are the source's first-order approximations, not exact or asymptotic statements with error terms; this page is an exposition of them.

**General approximation.** For a symmetric converging policy, the source treats the covariances between the infection indicators as negligible: one lemma sets a covariance to $0$ through the linear approximation above, and another assumes the remaining covariances are arbitrarily small. Under these approximations it derives

$$\mathbb{E}[\alpha(t)] \approx n(1-p)\,(1-q)^{\,np\sum_{i=0}^{t-1}\left((1 + nq(1-p))^i\prod_{j=1}^{i} p'(j)\right)}.$$

**Individual and Dorfman testing.** For the weak version of dynamic individual testing ($T$ individuals chosen uniformly at random from all $n$ individuals, isolated ones included, so that $1 - p'(t) = T/n$), if $(1 - \frac{T}{n})(1 + nq(1-p)) < 1$ the same approximations give

$$\lim_{t\to\infty}\mathbb{E}[\alpha_{\mathrm{weak}}(t)] \approx n(1-p)\,(1-q)^{\frac{np}{1 - (1 - T/n)(1 + nq(1-p))}},$$

which the source offers as a lower bound for the final expected number of never-infected individuals under the original individual-testing algorithm. The dynamic Dorfman-type algorithm randomly partitions the non-isolated individuals into $T/2$ groups, runs the $T/2$ group tests, and individually tests $T/2$ individuals drawn from positive groups. Its weak version discards the group results, partitions all $n$ individuals, and so amounts to testing $T/2$ uniformly chosen individuals; for it the same approximation holds with $T/n$ replaced by $T/(2n)$ under $(1 - \frac{T}{2n})(1 + nq(1-p)) < 1$, offered as a lower bound for the original Dorfman-type algorithm.

The stability conditions say that testing must remove infected individuals faster than the per-step reproduction factor $1 + nq(1-p)$ creates them; otherwise the epidemic is not brought under control.

## Expansion

In a symmetric policy the expected number of infected but unisolated individuals grows each step by the factor $1 + nq(1-p)$ (new infections among the susceptible pool, approximated by its initial size) and is thinned by the escape probability $p'(t)$; summing gives the cumulative infection pressure $np\sum_i (1 + nq(1-p))^i\prod_{j \le i}p'(j)$, and each susceptible avoids infection by every one of these infectious-person-steps with probability $1 - q$. For weak individual testing $p'(j) = 1 - T/n$ is constant, making the pressure a geometric series that converges exactly under the stated condition.

## Sources

- Batuhan Arasli and Sennur Ulukus, "Dynamic Infection Spread Model Based Group Testing", Algorithms 16 (2023), 25, <https://doi.org/10.3390/a16010025>; numbering as in arXiv:2201.08839: Section 2 (system model) and Theorems 1–3.
