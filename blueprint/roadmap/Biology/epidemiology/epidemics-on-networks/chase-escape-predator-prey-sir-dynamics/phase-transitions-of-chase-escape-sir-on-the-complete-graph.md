# Phase transitions of chase-escape SIR dynamics on the complete graph

**Model.** On the complete graph $K_{N+2}$ each vertex is susceptible ($S$), infected ($I$) or recovered ($R$). Every infected vertex infects each susceptible vertex at rate $\lambda > 0$, and every recovered vertex turns each infected vertex into a recovered one at rate $1$; susceptibles never become recovered directly. Start with one infected, one recovered and $N$ susceptible vertices, and stop the process as soon as no susceptible or no infected vertex remains. Let $E^N_{\mathrm{ext}}$ be the event that the susceptibles are exhausted (the infection reaches everyone), and let $S^{(N)}, I^{(N)}, R^{(N)}$ be the numbers of susceptible, infected and recovered vertices at absorption. $\mathrm{Exp}(1)$ denotes a standard exponential variable.

**Theorem (critical value).**

$$ \mathbb P(E^N_{\mathrm{ext}}) \xrightarrow[N\to\infty]{} \begin{cases} 0, & 0 < \lambda < 1,\\ \tfrac12, & \lambda = 1,\\ 1, & \lambda > 1.\end{cases} $$

**Theorem (final state).** As $N \to \infty$:

1. If $0 < \lambda < 1$: $S^{(N)}/N^{1-\lambda} \Rightarrow \mathrm{Exp}(1)^{\lambda}$, $(N - R^{(N)})/N^{1-\lambda} \Rightarrow \mathrm{Exp}(1)^\lambda$ and $I^{(N)} \to 0$ in probability.
2. If $\lambda = 1$: $\mathbb P(S^{(N)} = i) \to 2^{-(i+1)}$ for $i \ge 0$; $R^{(N)}/N \Rightarrow \tfrac12\delta_1 + (1+x)^{-2}\mathbf 1_{[0,1]}(x)\,dx$; $I^{(N)}/N$ converges in distribution to a law with density $(2-x)^{-2}$ on $[0,1]$ (total mass $\tfrac12$) and an atom $\tfrac12$ at $0$ (the event that the infection dies out).
3. If $\lambda > 1$: $S^{(N)} \to 0$ in probability, $R^{(N)}/N^{1/\lambda} \Rightarrow \mathrm{Exp}\big(\mathrm{Exp}(1)^{1/\lambda}\big)$ (an exponential variable with independent random rate) and $(N - I^{(N)})/N^{1/\lambda}$ has the same limit law.

**Theorem (mean outbreak sizes; two more transitions).** For $0 < \lambda < 1$,

$$ \mathbb E[I^{(N)}] \to 0 \ (\lambda < \tfrac12), \qquad \mathbb E[I^{(N)}] \to 1 \ (\lambda = \tfrac12), \qquad \mathbb E[I^{(N)}] \sim \tfrac12\Gamma(1 + 1/\lambda)\,N^{2 - 1/\lambda} \ (\tfrac12 < \lambda < 1), $$

and $N - \mathbb E[R^{(N)}] \sim \Gamma(\lambda + 1)N^{1-\lambda}$ for $\lambda < \frac{\sqrt5 - 1}{2}$, $\sim \big(\tfrac12\Gamma(1 + 1/\lambda) + \Gamma(\lambda+1)\big)N^{(3-\sqrt5)/2}$ at $\lambda = \frac{\sqrt5-1}{2}$, and $\sim \tfrac12\Gamma(1+1/\lambda)N^{2 - 1/\lambda}$ for $\frac{\sqrt5-1}{2} < \lambda < 1$. For $\lambda = 1$, $\mathbb E[I^{(N)}] \sim (1 - \ln 2)N$. Thus outbreaks are small for $\lambda \le \tfrac12$, of power-law size for $\tfrac12 < \lambda < 1$ and pandemic for $\lambda \ge 1$.

## Expansion

On the complete graph, a susceptible is infected at rate $\lambda I S$ and an infected vertex recovers at rate $R I$; after removing the common factor $I$ by a random time change (Athreya–Karlin embedding), infections and recoveries decouple into two independent Yule processes, $\mathcal Y$ of rate $\lambda$ and $\mathcal Z$ of rate $1$. The number of susceptibles is $\mathcal Y$ run backwards from its $N$-th jump and the number of recovered is $\mathcal Z$; absorption is the first time the reversed $\mathcal Y$ hits $0$ or the two sum to $N+2$. Since $e^{-\lambda t}\mathcal Y_t$ and $e^{-t}\mathcal Z_t$ converge to independent exponential variables, the reversed process needs time about $\lambda^{-1}\log N$ to exhaust the susceptibles while $\mathcal Z$ needs about $\log N$ to fill the population, and comparing these clocks gives the threshold $\lambda = 1$, the value $\tfrac12$ by symmetry at criticality, and the powers $N^{1-\lambda}$ and $N^{1/\lambda}$. Kendall's representation of a Yule process as a time-changed Poisson process conditional on its terminal value turns the limit laws into explicit computations; uniform integrability fails exactly at the extra thresholds $\lambda = \tfrac12$ and $\lambda = (\sqrt5-1)/2$, which is why the means change behaviour there while the distributional limits do not.

## Sources

- Igor Kortchemski, "A predator-prey SIR type dynamics on large complete graphs with three phase transitions", arXiv:1312.5678 (2013), Introduction (Theorems 1–4), Section 1 (Theorem 1.1, the Athreya–Karlin decoupling; Propositions 1.2–1.4 on Yule processes), Section 3 (Theorems 5–7). <https://doi.org/10.48550/arXiv.1312.5678>. Published version: Stochastic Processes and their Applications 125(3) (2015), 886–917, <https://doi.org/10.1016/j.spa.2014.10.005>; locators above refer to the arXiv version.
