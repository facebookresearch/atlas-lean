# Coalescent effective size under random population-size fluctuations

Let a haploid neutral Wright–Fisher population have size $M_N(\tau)$ in the generation $\tau$ steps into the past, where $N$ is a large scale parameter, and let $A_N(\tau)$ be the number of ancestors of a sample of fixed size $n$ in generation $\tau$. Let $A(t)$ be the block-counting process of Kingman's coalescent. A model has a **coalescent effective size** if there is a constant $c > 0$ with $A_N(\lfloor Nt\rfloor) \to A(ct)$ as $N \to \infty$; then $N_e = N/c$, and every sample property (the genealogy, hence all polymorphism data) is that of a constant-size Wright–Fisher population of size $N_e$, up to rescaling the mutation rate.

**Theorem (three regimes).**

1. *Fast fluctuations (averaging).* If $M_N(\tau) \in \{N_1, N_2, \dots\}$ with $N_i = x_i N$ forms an i.i.d. sequence with $P(M_N = N_i) = p_i$, or more generally a Markov chain with unique stationary law $(\pi_i)$ whose size-jump probabilities per generation are of order $N^{-\alpha}$ with $0 \le \alpha < 1$, then a coalescent effective size exists and is the stationary harmonic mean

$$N_e = \Bigl(\sum_i \frac{\pi_i}{N_i}\Bigr)^{-1}.$$

2. *Intermediate fluctuations (no averaging).* If the relative size process $X_N(t) = M_N(\lfloor Nt\rfloor)/N$ converges to a process $X$ with values in $I \subseteq (0, \infty)$ (a diffusion on $[a, b]$ with $a > 0$, a jump process with bounded rates, or a mixture), so that macroscopic size changes occur on the coalescent time scale, then the genealogy converges to $A(Y_t)$, Kingman's coalescent run on the random clock

$$Y_t = \int_0^t \frac{ds}{X(s)},$$

which is not linear in $t$ and depends on the initial size. No coalescent effective size exists.
3. *Slow fluctuations.* If size changes are rarer than coalescences on the $N$ scale, all coalescences occur before the first change, and the genealogy is that of a constant population at the initial size.

## Proof sketch

In the i.i.d. case two lineages fail to coalesce in one generation with probability $1 - 1/M_N(\tau)$, so conditioning on the sizes and averaging,

$$P(\text{no coalescence in } \lfloor Nt\rfloor \text{ generations}) = \Bigl(\sum_i p_i\bigl(1 - \tfrac{1}{x_i N}\bigr)\Bigr)^{\lfloor Nt\rfloor} \to \exp\Bigl(-t\sum_i \frac{p_i}{x_i}\Bigr),$$

a pairwise rate $c = \sum_i p_i/x_i$ and $N_e = N/c$. For a Markov size chain the same averaging happens between coalescences with $\pi$ in place of $p$. In the intermediate regime the conditional non-coalescence probability is $\prod_\tau (1 - 1/M_N(\tau)) \approx \exp(-\int_0^t ds/X_N(s))$, giving the cumulative intensity $Y_t$; with $k$ lineages the intensity is $\binom k2 Y_t$. Conditioning on a coalescence biases the size towards small values, so starting the size chain at stationarity does not restore a linear clock. In simulations of a two-state chain ($N_1 < N_2$, symmetric switching probability $q$), Sjödin et al. found that Fu and Li's $F$ detects departures from the constant-size model only for $q$ roughly between $1/(10N_2)$ and $10/N_1$; outside that window an effective size can be assumed.

## Depends on

- [Holding times of Kingman's coalescent](../../coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Proof depends on

- [Effective population size under fluctuating population size](effective-size-under-fluctuating-population-size.md)

## Sources

- P. Sjödin, I. Kaj, S. Krone, M. Lascoux and M. Nordborg, "On the meaning and existence of an effective population size", Genetics 169 (2005), 1061–1070, sections "The coalescent" and "Fluctuating population size" (Equations (1)–(2)) and Appendix (Equations (A1)–(A2)), <https://doi.org/10.1534/genetics.104.026799> (PMCID: PMC1449138).
