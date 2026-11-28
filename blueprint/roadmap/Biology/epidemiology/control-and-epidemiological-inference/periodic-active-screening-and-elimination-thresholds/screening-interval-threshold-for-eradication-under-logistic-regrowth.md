# Screening-interval threshold for eradication under logistic regrowth

Between screening rounds, the expected prevalence $f(t)$ in a community follows the logistic equation

$$\frac{df}{dt} = \kappa f\left(1 - \frac{f}{K}\right), \qquad \kappa > 0,\ 0 < K \le 1,$$

so that after the $n$-th round $f(S_n + \delta) = K / (1 + A_n e^{-\kappa\delta})$ with $A_n = K/f(S_n^+) - 1$. Each round, held every $\tau > 0$ time units, detects and removes the infected who participate (fraction $p \in (0,1]$) and test positive (sensitivity $s \in (0,1]$), so $f(S_n^+) = (1 - ps)\,f(S_n^-)$ with $ps < 1$.

Then $A_{n+1} = \alpha A_n + \beta$ with

$$\alpha = \frac{e^{-\kappa\tau}}{1 - ps}, \qquad \beta = \frac{ps}{1 - ps}, \qquad A_0 = \frac{K}{f(0)} - 1.$$

Let $\bar f_{n,n+1}$ be the expected average prevalence between rounds $n$ and $n+1$, and $\tau^* = -\log(1-ps)/\kappa$.

**Proposition (eradication threshold).**
1. If $\tau \le \tau^*$ then $\lim_{n\to\infty} \bar f_{n,n+1} = 0$.
2. If $\tau > \tau^*$ then $\lim_{n\to\infty} \bar f_{n,n+1} = K\left(\dfrac{\log(1-ps)}{\kappa\tau} + 1\right) > 0$.

The threshold $\tau^*$ does not depend on the carrying capacity $K$.

**Proposition (rounds to elimination).** If $f(0) > C$ and $\tau \le \tau^*$ (equivalently $\alpha \ge 1$), the expected prevalence first falls to at most $C$ after round $n^*$, where

$$n^* = \begin{cases} \log_{\alpha}\dfrac{K/C - 1 + \beta/(\alpha-1)}{A_0 + \beta/(\alpha-1)}, & \alpha > 1,\\[2ex] \dfrac{K/C - 1 - A_0}{\beta}, & \alpha = 1,\end{cases}$$

rounded up to an integer.

## Expansion

Just before round $n+1$, $f = K/(1 + A_n e^{-\kappa\tau})$; multiplying by $1-ps$ and inverting gives the affine recursion. Its solution is $A_n = \alpha^n (A_0 + \beta/(\alpha-1)) - \beta/(\alpha-1)$ for $\alpha \ne 1$ and $A_n = A_0 + n\beta$ for $\alpha = 1$. When $\alpha \ge 1$, $A_n$ increases to infinity, so prevalence after each round tends to $0$; solving $A_n \ge K/C - 1$ gives $n^*$. When $\alpha < 1$, $A_n \to A^* = \beta/(1-\alpha)$, a periodic endemic regime. Averaging the logistic solution over one period, $\frac{1}{\tau}\int_0^\tau K/(1 + A^* e^{-\kappa\delta})\,d\delta = K\bigl(1 + \tfrac{1}{\kappa\tau}\log\tfrac{1+A^*e^{-\kappa\tau}}{1+A^*}\bigr)$, which simplifies to the stated limit. In words, regrowth by a factor $e^{\kappa\tau}$ per interval must not exceed the depletion factor $(1-ps)^{-1}$. For the gambiense sleeping-sickness data analysed, annual screening eradicates only if the case-detection fraction $ps$ exceeds about $55\%$.

## Sources

- H. de Vries, A. P. M. Wagelmans, E. Hasker, C. Lumbala, P. Lutumba, S. J. de Vlas, J. van de Klundert, "Forecasting human African trypanosomiasis prevalences from population screening data using continuous time models", PLoS Computational Biology (2016), Eqs. (4)–(8) and (14), Propositions 1–3 and Lemma 1, <https://doi.org/10.1371/journal.pcbi.1005103>, PMCID PMC5033383.
