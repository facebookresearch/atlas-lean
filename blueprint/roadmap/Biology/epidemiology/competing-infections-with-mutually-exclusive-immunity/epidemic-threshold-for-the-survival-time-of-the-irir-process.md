# Epidemic threshold for the survival time of the IRIR process

**Model.** The IRIR process is a continuous-time Markov chain on a graph $G = (V,E)$ with $n$ vertices modelling two competing infections, each conferring immunity only against itself. Every vertex is in one of four states: infected by infection $1$ or $2$ ($I_1, I_2$), or recovered from infection $1$ or $2$ ($R_1, R_2$). A vertex in $R_{3-j}$ is susceptible to infection $j$ only. Along every edge, an $I_j$ vertex infects an $R_{3-j}$ neighbor at rate $\lambda_j$; every $I_j$ vertex recovers into $R_j$ at rate $\varrho_j$. Thus recovery from one infection makes a host susceptible to the other, and a new infection erases the old immunity. The *survival time* $T$ is the first time with $I_1 \cup I_2 = \emptyset$.

A graph has *density* $\delta \in (0,1]$ and is *perfectly mixed* if the edge density between every pair of nonempty vertex sets equals $\delta$ (e.g. cliques with $\delta = 1$). It is $(p,\beta)$-*jumbled* if $\big|e(X,Y) - p|X||Y|\big| \le \beta\sqrt{|X||Y|}$ for all vertex sets $X, Y$. Write $\lambda_j^e = \lambda_j\delta$ for the effective infection rates.

**Theorem (threshold).** Let $\varrho_1, \varrho_2 > 0$ be constants, $\lambda_j^e = c_j/n$ with constants $c_j > 0$, and let $c > 0$ be a constant.
1. (Long survival.) On a perfectly mixed graph, or more generally on a $(p, pn/k)$-jumbled graph with $k = \omega(\ln n)$, if

$$\frac{\varrho_1}{\lambda_1^e} + \frac{\varrho_2}{\lambda_2^e} < (1-c)\,n$$

and both infections start with at least $\varepsilon_h n$ infected vertices for a small enough constant $\varepsilon_h > 0$, then there is a constant $c_T > 0$ with

$$\Pr\left[T \le \exp\!\Big(\frac{c_T n}{8\ln n}\Big)\right] \le 2\exp\!\Big(-\frac{c_T n}{2\ln n}\Big)$$

for all large $n$; the survival time is super-polynomial with high probability.
2. (Fast extinction.) On a perfectly mixed graph, if $\dfrac{\varrho_1}{\lambda_1^e} + \dfrac{\varrho_2}{\lambda_2^e} > (1+c)\,n$, then $\mathbb{E}[T] = O(n\ln n)$.

Hence $n$ is a sharp epidemic threshold for $\varrho_1/\lambda_1^e + \varrho_2/\lambda_2^e$. Since Erdős–Rényi graphs $G(n,p)$ with $p = k/n \le 0.99$ are almost surely suitably jumbled, the super-polynomial lower bound holds for them when $k = \omega(\ln^2 n)$.

## Expansion

In the mean-field limit the recovered pools act as each other's susceptible pools: $R_2$ feeds infection $1$ and $R_1$ feeds infection $2$, so the infections are cooperative and survive together or die together. The endemic equilibrium has $|R_1| = \varrho_2/\lambda_2^e$ and $|R_2| = \varrho_1/\lambda_1^e$, which fits in the population exactly when their sum is below $n$; this explains the threshold. For the lower bound, a potential built from a Lyapunov function of the mean-field equilibrium is a supermartingale with negative drift and bounded steps on a linear-width region around the equilibrium, and the negative drift theorem gives exponential-in-$n/\ln n$ escape times. Above the threshold the infected count has drift towards $0$, and additive drift yields the $O(n\ln n)$ bound. This is the two-infection analogue of the threshold $\varrho/\lambda^* = n$ for the SIS process on cliques.

## Sources

- N. Klodt, M. S. Krejca, "A Tight Epidemic Threshold for Competing Stochastic Infection Processes with Mutually Exclusive Immunity", arXiv:2605.19933 (2026), model and graph-class definitions (Preliminaries), main theorem on perfectly mixed graphs and its corollaries for jumbled and Erdős–Rényi graphs, and the fast die-out theorem (Section 4), <https://doi.org/10.48550/arXiv.2605.19933>.
