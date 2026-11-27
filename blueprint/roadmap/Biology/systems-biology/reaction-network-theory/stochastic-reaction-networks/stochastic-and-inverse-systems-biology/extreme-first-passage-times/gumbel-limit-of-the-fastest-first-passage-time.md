# Gumbel limit of the fastest of many independent first passage times

Let $\tau_1, \tau_2, \dots$ be independent and identically distributed nonnegative random variables (first passage times of independent diffusive searchers) with survival function $S(t) = \mathbb{P}(\tau_1 > t)$, and let

$$T_N = \min\{\tau_1, \dots, \tau_N\}$$

be the fastest first passage time among $N$ searchers. Assume the short-time behaviour

$$1 - S(t) \sim A\, t^{p}\, e^{-C/t} \quad \text{as } t \to 0^+,$$

for constants $A > 0$, $C > 0$ and $p \in \mathbb{R}$, where $f \sim g$ means $f/g \to 1$.

Say $X \sim \mathrm{Gumbel}(b, a)$ (location $b \in \mathbb{R}$, scale $a > 0$) when $\mathbb{P}(X > x) = \exp(-\exp((x - b)/a))$ for all $x \in \mathbb{R}$.

**Theorem (Lawley 2020, Theorem 1).** Under these assumptions,

$$\frac{T_N - b_N}{a_N} \xrightarrow{d} X \sim \mathrm{Gumbel}(0, 1) \quad \text{as } N \to \infty,$$

where, if $p = 0$,

$$b_N = \frac{C}{\ln(AN)}, \qquad a_N = \frac{b_N}{\ln(AN)},$$

and, if $p \neq 0$,

$$b_N = \frac{C}{p\, W}, \qquad a_N = \frac{b_N}{p\,(1 + W)}, \qquad W = \begin{cases} W_0\!\left(\tfrac{C}{p} (AN)^{1/p}\right), & p > 0,\\[2pt] W_{-1}\!\left(\tfrac{C}{p} (AN)^{1/p}\right), & p < 0,\end{cases}$$

with $W_0$ and $W_{-1}$ the principal and lower branches of the Lambert $W$ function: for $x > -e^{-1}$, $W_0(x)$ is the unique $y > -1$ with $y e^y = x$, and for $-e^{-1} \le x < 0$, $W_{-1}(x)$ is the unique $y \le -1$ with $y e^y = x$. For $p < 0$ the argument $\tfrac{C}{p}(AN)^{1/p}$ is negative and tends to $0$, so it lies in $[-e^{-1}, 0)$ for all large $N$, and $b_N$, $a_N$ are defined for those $N$.

**Theorem (Lawley 2020, Theorem 2).** The same convergence holds, for every $p \in \mathbb{R}$, with the elementary rescalings

$$a_N' = \frac{C}{(\ln N)^2}, \qquad b_N' = \frac{C}{\ln N} + \frac{C p \ln(\ln N)}{(\ln N)^2} - \frac{C \ln(A C^{p})}{(\ln N)^2}.$$

**Theorem (Lawley 2020, Theorem 3).** If in addition $\mathbb{E}[T_N] < \infty$ for some $N \ge 1$, then for every positive integer $m$, $\mathbb{E}\big[((T_N - b_N)/a_N)^m\big] \to \mathbb{E}[X^m]$ for $X \sim \mathrm{Gumbel}(0,1)$. (Only integer orders are stated: $X$ takes negative values with positive probability, so $X^m$ is not real-valued for fractional $m$.) In particular

$$\mathbb{E}[T_N] = b_N - \gamma a_N + o(a_N), \qquad \operatorname{Var}(T_N) = \frac{\pi^2}{6} a_N^2 + o(a_N^2),$$

where $\gamma$ is the Euler–Mascheroni constant. Hence $\mathbb{E}[T_N] \sim C / \ln N$.

## Depends on

- [Principal-branch preimages of the Lambert map](../../../../../../Analysis/special-functions/elementary-transcendental-functions/lambert-w-function/exists-unique-lambert-map-preimage.md)
- [Lower-branch preimages of the Lambert map](../../../../../../Analysis/special-functions/elementary-transcendental-functions/lambert-w-function/exists-unique-lambert-map-lower-preimage.md)

## Expansion

Because the $\tau_n$ are independent, $\mathbb{P}(T_N > t) = S(t)^N$. Since $1 - S(t) = e^{-C/t + \ln(A t^p) + o(1)}$ as $t \to 0^+$, the minimum is governed by the extreme left tail of $\tau_1$. The tail lies in the Gumbel domain of attraction for minima, and the location $b_N$ solves $N(1 - S(b_N)) \approx 1$, i.e. $A b_N^{p} e^{-C/b_N} = 1/N$; solving this equation in closed form gives the Lambert $W$ expressions, and expanding it for large $N$ gives the iterated-logarithm rescalings of Theorem 2. Moment convergence follows from Pickands' theorem on moments of extremes once one moment of $T_N$ is finite.

## Sources

- S. D. Lawley, "Distribution of extreme first passage times of diffusion", Journal of Mathematical Biology 80 (2020), 2301–2325, Theorems 1–3, <https://doi.org/10.1007/s00285-020-01496-9>.
