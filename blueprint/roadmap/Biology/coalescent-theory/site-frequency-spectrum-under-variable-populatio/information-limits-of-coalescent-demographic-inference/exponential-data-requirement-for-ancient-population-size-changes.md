# Exponential data requirement for detecting ancient population-size changes

Let $N : [0,\infty) \to (0,\infty)$ be a population-size history (time measured backward), under which a pair of lineages coalesces at instantaneous rate $1/N(t)$, so a pairwise coalescence time $\tau$ satisfies $\mathbb P(\tau > t) = \exp\big(-\int_0^t N(s)^{-1}\,ds\big)$. Fix constants $a, b, S > 0$ and $T \ge 0$, and set $N_0 = N(0)$.

Consider two hypotheses that agree with $N$ on $[0,T)$ and on $[T+S,\infty)$ and differ only on the window $[T, T+S)$: under $H_1$ the size there is the constant $a N_0$, under $H_2$ the constant $b N_0$. Suppose $L$ independent pairwise coalescence times are observed and each hypothesis has prior probability $1/2$.

**Theorem.** For every classifier the Bayes error is at least $(1 - \mathcal E)/2$, where

$$\mathcal E^2 \le 2L\,\exp\Big(-\int_0^T \frac{dt}{N(t)}\Big)\Big(1 - e^{-\frac{S}{2N_0}\frac{a+b}{ab}}\Big)\frac{(\sqrt a - \sqrt b)^2}{a+b} \le 2L\,\exp\Big(-\int_0^T \frac{dt}{N(t)}\Big)\min\Big\{\frac{S}{2N_0}, \frac{ab}{a+b}\Big\}\frac{(\sqrt a - \sqrt b)^2}{ab}.$$

Equivalently, the probability of identifying the true hypothesis is at most $(1+\mathcal E)/2$. To distinguish the two histories with constant probability one therefore needs

$$L \gtrsim \exp\Big(\int_0^T \frac{dt}{N(t)}\Big),$$

i.e. a number of independent loci exponential in the coalescent depth of the window. For a constant history $N \equiv N_0$ this is $L \gtrsim e^{T/N_0}$. Conditioning instead on the number $\ell$ of pairs that have not coalesced by time $T$ gives the companion bound $\Delta^2 \le 2\ell\,(\sqrt b - \sqrt a)^2/(a+b)$.

## Expansion

The Bayes error between two simple hypotheses is $\tfrac12(1 - d_{TV}(P_1^{\otimes L}, P_2^{\otimes L}))$, and the total variation distance is bounded through the Hellinger distance, which tensorizes over the $L$ independent loci. A pair contributes nothing to distinguishing the histories unless it survives to time $T$, which happens with probability $\exp(-\int_0^T N^{-1})$; conditional on survival the two laws of $\tau - T$ differ only through exponential rates $1/(aN_0)$ versus $1/(bN_0)$ on a window of length $S$, and their squared Hellinger distance is at most $(1 - e^{-\frac{S}{2N_0}\frac{a+b}{ab}})(\sqrt a - \sqrt b)^2/(a+b)$. A matching simple reconstruction algorithm (binning time into intervals and estimating the effective constant size per interval from the fraction of pairs coalescing in it) achieves the bound up to constants.

## Sources

- Junhyong Kim, Elchanan Mossel, Miklós Z. Rácz, Nathan Ross, "Can one hear the shape of a population history?", *Theoretical Population Biology* 100 (2015), 26–38, <https://doi.org/10.1016/j.tpb.2014.12.002>; preprint arXiv:1402.2424, <https://doi.org/10.48550/arXiv.1402.2424>. Numbering of the arXiv version: Theorem 1.1, Theorem 2.4, Section 3.
