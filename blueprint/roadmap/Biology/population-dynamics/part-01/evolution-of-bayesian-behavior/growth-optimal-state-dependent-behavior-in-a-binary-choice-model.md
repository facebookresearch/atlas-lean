# Growth-optimal state-dependent behavior in a binary choice model

**Model.** In each generation $t$ every individual observes information $S$ about the environment and chooses action $a$ with probability $f(S)\in[0,1]$ and action $b$ otherwise, then produces $x_a$ or $x_b$ offspring and dies; offspring inherit the behavior $f(\cdot)$. Conditioned on the state, the pair $(x_a,x_b)$ is i.i.d. over generations and identical for all individuals of a generation (systematic risk); the state process is stationary and ergodic; and the state, $(x_a,x_b)$ and $\log(fx_a+(1-f)x_b)$ for every $f\in[0,1]$ have finite second moments, marginally and conditioned on the state (Assumptions 1–4). Let $n^f_T$ be the number of type-$f$ individuals at generation $T$.

**Growth rate.** Almost surely

$$\frac1T\log n^f_T\ \longrightarrow\ \alpha(f)=\mathbb E_{(x_a,x_b,S)}\Big[\log\big(f(S)x_a+(1-f(S))x_b\big)\Big],$$

so the type with the largest $\alpha$ dominates the population.

**Proposition (stationary environment, state-dependent behavior).** The growth-optimal behavior maximizes the conditional expected log fitness for each observed $S$,

$$f^*(S)=\arg\max_{f\in[0,1]}\ \mathbb E\big[\log(fx_a+(1-f)x_b)\,\big|\,S\big],$$

and explicitly

$$f^*(S)=\begin{cases}1 & \text{if }\mathbb E[x_b/x_a\mid S]<1,\\ \text{the root of }\ \mathbb E\Big[\dfrac{x_a-x_b}{f x_a+(1-f)x_b}\,\Big|\,S\Big]=0 & \text{if }\mathbb E[x_a/x_b\mid S]\ge1\text{ and }\mathbb E[x_b/x_a\mid S]\ge1,\\ 0 & \text{if }\mathbb E[x_a/x_b\mid S]<1.\end{cases}$$

With no information ($S$ trivial) this reduces to the constant growth-optimal (bet-hedging) behavior; if additionally one action leaves offspring only in one of two environmental states, $f^*$ equals the probability of that state (probability matching). If the environment is nonstationary but independent over time, the dominant constant behavior uses the time-averaged expectations.

## Expansion

Conditioning on all available information turns $\alpha(f)$ into an average over $S$ of separate concave problems, so the optimum is pointwise in $S$; the boundary cases are where the derivative at $f=1$ or $f=0$ already has the right sign. The selected behavior is an expected-utility maximizer with logarithmic utility, where the log is endogenous (it comes from systematic risk shared by all individuals) and the expectation is over the posterior of the environment given $S$. Read generation by generation, the update of the type frequencies is Bayes' rule with the previous frequency as prior and fitness as likelihood. No individual reasons or encodes probabilities; selection alone produces Bayesian-looking behavior. When states are nonstationary or sampling is costly, the growth-optimal rule uses only a few recent observations, an evolutionary origin for finite memory.

## Sources

- A. W. Lo, R. Zhang, "The evolutionary origin of Bayesian heuristics and finite memory", *iScience* 24(8):102853 (2021), equations (1), (2), (5), (6) and (13)–(19), Assumptions 1–4, Propositions 1–3 (STAR Methods), <https://doi.org/10.1016/j.isci.2021.102853>, PMCID: PMC8340130.
