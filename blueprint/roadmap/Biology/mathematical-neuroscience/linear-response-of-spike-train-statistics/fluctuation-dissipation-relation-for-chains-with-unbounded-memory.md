# Fluctuation–dissipation relation for chains with unbounded memory

**Setting.** A network of $N$ neurons in discrete time produces spike patterns $\omega(n) \in \{0,1\}^N$; a spike train is $\omega = (\omega(n))_{n \in \mathbb{Z}}$. Its statistics are given by a **chain with unbounded memory**: transition probabilities $P(\omega(n) \mid \omega_{-\infty}^{n-1})$ that may depend on the entire past, written through a **normalized potential** $\phi(n, \omega) = \log P(\omega(n) \mid \omega_{-\infty}^{n-1})$. Under continuity of $\phi$ in the past (and the usual uniqueness conditions) such a system has a probability measure on spike trains consistent with it, a Gibbs distribution; in the spontaneous regime this is $\mu^{(sp)}$ with potential $\phi^{(sp)}$. A weak time-dependent stimulus switched on after time $n_0$ changes the potential to $\phi = \phi^{(sp)} + \delta\phi$, with $\delta\phi(r, \cdot) = 0$ for $r \le n_0$, and the measure to $\mu$.

**Theorem (linear response).** Let $f(t, \omega)$ be an observable with finite range $R_f = D_f + 1$ (depending only on $\omega_{n - D_f}^{n}$, $n = \lfloor t \rfloor$) and assume $n - n_0 > R_f$. To first order in $\delta\phi$,

$$\mathbb{E}_\mu[f(t, \cdot)] - \mathbb{E}^{(sp)}[f(t, \cdot)] = \sum_{r = n_0 + 1}^{\lfloor t \rfloor} \mathcal{C}^{(sp)}\big[f(t, \cdot),\ \delta\phi(r, \cdot)\big],$$

where $\mathcal{C}^{(sp)}[f, g] = \mathbb{E}^{(sp)}[fg] - \mathbb{E}^{(sp)}[f]\,\mathbb{E}^{(sp)}[g]$ is the correlation in the spontaneous Gibbs distribution. The series has a limit as $n_0 \to -\infty$ when these correlations decay fast enough, e.g. exponentially.

## Expansion

The evoked block probabilities are $P(\omega_{n_0+1}^n \mid \omega_{-\infty}^{n_0}) = P^{(sp)}(\cdot)\,e^{\delta\Phi}$ with $\delta\Phi = \sum_{r = n_0+1}^n \delta\phi(r, \cdot)$. Expanding the exponential to first order breaks normalization, and renormalizing (using that $\Phi^{(sp)}$ is already a log-conditional probability, so its partition function is $1$) gives $P^{(1)} = P^{(sp)}\big(1 + \delta\Phi - \mathbb{E}^{(sp)}[\delta\Phi \mid \omega_{-\infty}^{n_0}]\big)$. Averaging $f$, which does not depend on the past before $n_0$, turns the conditional expectation into an unconditional one and yields the sum of correlations. This is the analogue of the fluctuation–dissipation theorem of statistical physics for non-stationary, non-Markovian spike statistics: the response to a stimulus is predicted from correlations measured in spontaneous activity. For a conductance-based discrete-time integrate-and-fire network, $\delta\phi$ can be expanded explicitly in the stimulus, separating the contributions of stimulus, intrinsic dynamics and synaptic connectivity to the change in spike correlations.

## Sources

- B. Cessac, I. Ampuero, R. Cofré, "Linear response of general observables in spiking neuronal network models", Entropy 23(2) (2021) 155, Section 2 (chains with unbounded memory, normalized potentials, Theorem 1), Section 3.1 (first-order expansion) and Section 3.2 (Eq 16), Section 4 (integrate-and-fire example), <https://doi.org/10.3390/e23020155>, PMCID PMC7911777.
