# Fixation time of a moderately selected sweep in the Moran model

**Model.** In a two-type Moran model of constant size $N$, let $X_1^N(t)$ be the number of mutants and $X_0^N(t) = N - X_1^N(t)$ the number of residents. From state $(N-k, k)$ the chain jumps to $(N-k-1, k+1)$ at rate $(1 + a\varphi_N)\,k(N-k)/N$ and to $(N-k+1, k-1)$ at rate $k(N-k)/N$, so the mutant has selective advantage $s_N = a\varphi_N$ with $a > 0$. Assume $\varphi_N \le 1$ and $b_N := -\log_N \varphi_N \to b \in [0, 1)$; selection is **moderate** if $b \in (0,1)$ (for example $\varphi_N = N^{-b}$) and **quasi-strong** if $b = 0$ and $\varphi_N \to 0$ (for example $\varphi_N = 1/\log N$). Start from a single mutant, $X^N(0) = (N-1, 1)$, and let $\mathcal T_1^N$ be the fixation time of the mutant.

**Statement.** Conditional on fixation $\{\mathcal T_1^N < \infty\}$ (an event of probability $\sim a\varphi_N/(1 + a\varphi_N)$),

$$\frac{\mathcal T_1^N}{\varphi_N^{-1}\log N} \;\longrightarrow\; \frac{2(1-b)}{a} \quad\text{in probability as } N \to \infty.$$

For strong selection ($\varphi_N \equiv 1$, $b = 0$) this recovers the classical sweep duration $\tfrac{2}{s}\log N$.

## Depends on

- [Duration of a logistic sweep between two frequencies](sweep-duration.md)

## Expansion

The sweep splits into five phases. A surviving mutant family, a slightly supercritical branching process, needs time $o(\varphi_N^{-1}\log N)$ to reach size $\log N/\varphi_N$ (Phase 1), then grows exponentially at rate $a\varphi_N$ from $N^{b}$ (the order of $\varphi_N^{-1}$) up to order $N$, which takes $(1-b)\log N/(a\varphi_N)$ (Phase 2). The logistic middle phase is short (Phase 3). The residents then decline as a slightly subcritical branching process from order $N$ down to order $N^{b}$, again taking $(1-b)\log N/(a\varphi_N)$ (Phase 4), and the last $\log N/\varphi_N$ residents die out in negligible time (Phase 5). Couplings of $X_1^N$ and $X_0^N$ to binary Galton–Watson processes make the two exponential phases precise.

## Sources

- F. Boenkost, F. Hermann, A. Tóbiás and A. Wakolbinger, Logarithmic scaling of selective sweep curves: from tents to houses, arXiv (2026). <https://doi.org/10.48550/arXiv.2605.10617> (Theorem 2.5 part I.1, Propositions 3.1 to 3.5, Remark 2.1.)
