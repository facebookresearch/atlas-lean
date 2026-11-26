# Invasion, fixation and coexistence in a Moran model with competition-induced dormancy

**Model.** A population of fixed size $N$ contains type-$1$ individuals (always active) and type-$2$ individuals, which are active ($2a$) or dormant ($2d$). With counts $(\ell, n, m)$ of types $1$, $2a$, $2d$, and parameters $s \in (0,1)$ (selective advantage of type $1$), $p \in (0,1)$ (probability that competitive pressure induces dormancy instead of death), $\sigma > 0$ (resuscitation rate) and $\kappa \ge 0$ (death rate of dormant individuals, replaced by the offspring of a uniformly chosen individual), the transitions are
$$\begin{aligned}
(\ell+1, n-1, m) &\ \text{at rate } \tfrac1N \ell n \tfrac{1+s}{2}(1-p), & (\ell-1, n+1, m) &\ \text{at rate } \tfrac1N \ell n\tfrac{1-s}{2},\\
(\ell, n-1, m+1) &\ \text{at rate } \tfrac1N\big(\ell n\tfrac{1+s}{2} + n(n-1)\big)p, & (\ell, n+1, m-1) &\ \text{at rate } \sigma m + \kappa m \tfrac nN,\\
(\ell+1, n, m-1) &\ \text{at rate } \kappa m \tfrac{\ell}{N}. &&
\end{aligned}$$
Let $T^i_0$ be the extinction time of type $i$ and $T^{co}_\beta$ the hitting time of a $\beta$-neighborhood of the interior (coexistence) equilibrium of the large-$N$ limit

$$\dot x_1 = x_1\Big(x_{2a}\big(s - \tfrac{1+s}{2}p\big) + \kappa(1 - x_1 - x_{2a})\Big), \qquad \dot x_{2a} = -s x_1x_{2a} - p x_{2a}^2 + (1 - x_1 - x_{2a})(\kappa x_{2a} + \sigma).$$

**Critical parameters.** With $D = p(1+s) - 2s$, let

$$\tilde\kappa = \frac{-2D\sigma - \sqrt{4D^2\sigma^2 - 4(2D - 4p)\sigma D^2}}{4D - 8p}, \qquad \kappa' = \frac{\sigma}{s}\Big(\frac{1+s}{2}p - s\Big),$$

and let $q_{2a}$ be the extinction probability of the branching approximation started from one active type-$2$ individual, the smallest solution with $q_{2a}, q_{2d} \in [0,1]$ of

$$q_{2a} = \tfrac{1+s}{2}(1-p) + \tfrac{1-s}{2}q_{2a}^2 + p\tfrac{1+s}{2}q_{2d}, \qquad q_{2d} = \tfrac{\sigma}{\sigma+\kappa}q_{2a} + \tfrac{\kappa}{\sigma+\kappa}.$$

The type-$2$ monomorphic equilibrium has $\bar x_{2a} = \frac{\kappa - \sigma + \sqrt{(\kappa-\sigma)^2 + 4\sigma(p+\kappa)}}{2(p+\kappa)}$.

**Theorem.** Assume $p \ne \frac{2s}{1+s}$, $\kappa \notin \{\tilde\kappa, \kappa'\}$, and start from one active mutant, $(N-1, 1, 0)$. For all sufficiently small $\beta > 0$, $\lim_N \mathbb{P}(T^2_0 < T^1_0 \wedge T^{co}_\beta) = q_{2a}$, and on that event $T^2_0/\log N \to 0$ in probability. On the complementary event (asymptotic probability $1 - q_{2a}$):
- if $p < \frac{2s}{1+s}$, type $1$ fixates for every $\kappa \ge 0$;
- if $p > \frac{2s}{1+s}$ and $\sigma > \frac{2s^2}{p(1-s)}$: type $1$ fixates for $\kappa > \kappa'$, type $2$ fixates for $0 \le \kappa < \tilde\kappa$, and the two types coexist (the process reaches the coexistence equilibrium) for $\tilde\kappa < \kappa < \kappa'$.

So a selectively inferior type can invade, fix or coexist purely through dormancy, provided dormant individuals do not die too fast.

## Depends on

- [Wright–Fisher diffusion with a strong seed bank](../../coalescent-theory/structured-coalescent/seed-bank-coalescent/wright-fisher-diffusion-with-a-strong-seed-bank.md)

## Expansion

While the mutant is rare, its active and dormant counts form a two-type branching process; invasion happens with probability $1 - q_{2a}$, else it dies in $o(\log N)$ time. Once it reaches a macroscopic fraction, the rescaled process follows the two-dimensional ODE, whose phase portrait is classified by the stability of the boundary equilibria: $(1,0)$ is stable iff $\kappa > \kappa'$, and $(0, \bar x_{2a})$ is stable iff $p > \frac{2s}{1+s}$ and $\kappa < \tilde\kappa$. When both are unstable a unique interior equilibrium attracts. The final phase near a boundary equilibrium is again a branching-process extinction of the minority type, which takes $O(\log N)$ time.

## Sources

- J. Blath, B. Le Duigou and A. Tóbiás, "The interplay of selection and dormancy in a Moran model can lead to coexistence of types", arXiv:2602.24106 (2026), Section 2, Theorem 2.10 and Equations defining $\tilde\kappa$, $\kappa'$ and $q_{2a}$, <https://doi.org/10.48550/arXiv.2602.24106>.
