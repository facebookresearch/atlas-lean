# Herd immunity in trait-heterogeneous SIR and SEIR models holds iff the mean recovery time is finite

**Model.** Let $(\Omega, dx)$ be a probability space of individual traits. Individuals with trait $x$ recover at rate $\gamma(x) \ge 0$, and a susceptible with trait $x$ is infected by infectives with trait $y$ at rate $\beta(x,y)$. With $S(t,x), I(t,x), R(t,x)$ the probabilities that an individual of trait $x$ is susceptible, infectious or recovered,

$$
\partial_t S(t,x) = -S(t,x)\int_\Omega \beta(x,y)I(t,y)\,dy, \quad
\partial_t I(t,x) = S(t,x)\int_\Omega \beta(x,y)I(t,y)\,dy - \gamma(x)I(t,x), \quad
\partial_t R(t,x) = \gamma(x)I(t,x),
$$

and population averages $S(t) = \int_\Omega S(t,x)\,dx$ etc. Assume $0 < \beta_{\min} \le \beta(x,y) \le \beta_{\max} < \infty$, $R(0) = 0$ and $I(0) > 0$. The model has the *herd immunity property* if $S(\infty) = \lim_{t\to\infty}S(t) > 0$, i.e. the epidemic burns out before infecting everyone.

**Statement.**

1. *SIR.* The heterogeneous SIR model has the herd immunity property if and only if the mean recovery time is finite:

$$
\mathbb{E}\left[\frac{1}{\gamma(x)}\right] = \int_\Omega \frac{dx}{\gamma(x)} < \infty
$$

(with $1/\gamma = +\infty$ where $\gamma = 0$).
2. *SEIR.* The same equivalence holds for the heterogeneous SEIR model, with an exposed class $E$ leaving at trait-dependent rate $\alpha(x)$, $0 < \alpha_{\min} \le \alpha(x) \le \alpha_{\max} < \infty$, under $R(0) = 0$ and $E(0) + I(0) > 0$.

In particular the mean recovery *rate* $\mathbb{E}[\gamma]$ does not decide herd immunity. With $\beta = 1/4$ and $\mathbb{E}[\gamma] = 1/6$ in each case: constant $\gamma = 1/6$ leaves $S(\infty) \approx 0.42$; a two-group population with $\gamma \in \{0, 1/3\}$ equally likely, or $\gamma(x) = x/3$ on $\Omega = [0,1]$ (where $\mathbb{E}[1/\gamma] = \infty$), infects everyone, $S(\infty) = 0$; while $\gamma(x) = \sqrt x/4$ (where $\mathbb{E}[1/\gamma] = 8$) restores herd immunity.

## Depends on

- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Proof sketch

Since $I(t,y) = \gamma(y)^{-1}\partial_t R(t,y)$, integrating $\partial_t\ln S(t,x)$ gives the heterogeneous final-size identity

$$
S(t,x) = S(0,x)\exp\left\{-\int_\Omega \frac{\beta(x,y)}{\gamma(y)}\bigl(R(t,y) - R(0,y)\bigr)\,dy\right\}.
$$

If $\mathbb{E}[1/\gamma] < \infty$, then $R \le 1$ gives $S(\infty) \ge S(0)\exp(-\beta_{\max}\mathbb{E}[1/\gamma]) > 0$. Conversely, if $\gamma = 0$ on a set $Z$ of positive measure, infectives in $Z$ never recover, $I_Z(t) = \int_Z I(t,y)\,dy$ obeys a logistic-type lower bound and tends to $1$, so every $S(t,x)$ decays exponentially and $S(\infty) = 0$. If $\gamma > 0$ a.e., the early phase with $I(t) \ge I(0)/2$ forces $S(\infty,x) \le C < 1$ uniformly, and since $I(t,x) \to 0$ this gives $R(\infty,y) \ge 1 - C$; inserting this into the final-size identity yields $S(\infty) \le S(0)\exp(-\beta_{\min}(1-C)\mathbb{E}[1/\gamma])$, which is $0$ when $\mathbb{E}[1/\gamma] = \infty$. The SEIR case is analogous, with the bounded exposed-period rates $\alpha$ ensuring that all infected mass eventually passes through $I$.

## Sources

- Gabriel Turinici, "The impact of recovery rate heterogeneity in achieving herd immunity", *Bollettino dell'Unione Matematica Italiana* 18 (2025), 1171–1179, <https://doi.org/10.1007/s40574-025-00471-w>. Preprint version: arXiv:2411.13130v2 (2025), Definition 1, Lemma 2, Propositions 3 and 5, <https://doi.org/10.48550/arXiv.2411.13130>.
