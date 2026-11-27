# MFALK model and its globally attracting steady state

**Model.** For $n$ sites with occupancies $x_i(t) \in [0,1]$ and nonnegative rates $\lambda_i, \gamma_i$ ($i = 0,\dots,n$; forward transition from site $i$ to $i+1$ and backward transition from $i+1$ to $i$), $\beta_i$ (attachment) and $\alpha_i$ ($i = 1,\dots,n$; detachment), the MFALK is

$$\dot x_i = \lambda_{i-1}x_{i-1}(1-x_i) + \gamma_i x_{i+1}(1-x_i) + \beta_i(1-x_i) - \lambda_i x_i(1-x_{i+1}) - \gamma_{i-1}x_i(1-x_{i-1}) - \alpha_i x_i$$

for $1 < i < n$, with

$$\dot x_1 = \lambda_0(1-x_1) + \gamma_1x_2(1-x_1) + \beta_1(1-x_1) - \lambda_1x_1(1-x_2) - \gamma_0x_1 - \alpha_1x_1,$$

$$\dot x_n = \lambda_{n-1}x_{n-1}(1-x_n) + \gamma_n(1-x_n) + \beta_n(1-x_n) - \lambda_nx_n - \gamma_{n-1}x_n(1-x_{n-1}) - \alpha_nx_n .$$

The output rate is $R = (\lambda_n + \alpha_n)x_n - (\gamma_n + \beta_n)(1-x_n)$. With $\alpha_i = \beta_i = \gamma_i = 0$ it reduces to the ribosome flow model, the mean-field approximation of the totally asymmetric exclusion process. The unit cube $C^n = [0,1]^n$ is invariant.

**Results.** Assume

$$\text{(P)}\quad \lambda_i + \beta_{i+1} > 0\ \ \forall i \in\{0,\dots,n\}\quad\text{or}\quad \gamma_i + \alpha_{i+1} > 0\ \ \forall i\in\{0,\dots,n\},$$

with $\alpha_{n+1} = \beta_{n+1} = 0$.

1. (Persistence.) Under (P), for every $\tau > 0$ there is $d \in (0, 1/2]$ with $d \le x_i(t+\tau, a) \le 1-d$ for all $a \in C^n$, all $i$ and all $t \ge 0$.
2. ($\ell_1$ contraction.) With $\eta = \max\{-\lambda_0-\gamma_0-\alpha_1-\beta_1,\ -\alpha_2-\beta_2,\ \dots,\ -\alpha_{n-1}-\beta_{n-1},\ -\lambda_n-\gamma_n-\alpha_n-\beta_n\} \le 0$, every two solutions satisfy $|x(t,a) - x(t,b)|_1 \le e^{\eta t}|a-b|_1$.
3. (Contraction after small overshoot.) If moreover $\lambda_i + \gamma_i > 0$ for $i = 1,\dots,n-1$, then for every $\varepsilon > 0$ there is $\ell(\varepsilon) > 0$ with $|x(t,a) - x(t,b)|_1 \le (1+\varepsilon)e^{-\ell t}|a-b|_1$.
4. (Global stability.) Under the hypotheses of 3, the MFALK has a unique steady state $e \in \operatorname{int}(C^n)$ and $x(t,a) \to e$ for every $a \in C^n$.

## Expansion

The Jacobian is tridiagonal with nonnegative off-diagonal entries, and each column sum equals minus the direct loss to the environment from that site, so the matrix measure induced by the $\ell_1$ norm is at most $\eta$, giving item 2. When $\eta = 0$ this only shows nonexpansion; persistence moves every trajectory into the interior after any positive time, where the Jacobian is irreducible, and this yields contraction with an arbitrarily small overshoot. A steady state exists in the compact convex invariant cube by Brouwer's theorem, lies in the interior by persistence, and attracts every trajectory by contraction. The condition $\lambda_i + \gamma_i > 0$ is no restriction: if it fails at $i$ the chain splits into two independent MFALKs.

## Sources

- Zarai Y, Margaliot M, Tuller T, "A deterministic mathematical model for bidirectional excluded flow with Langmuir kinetics", PLoS One (2017), Section 1, Eqs. (1)–(3); Section 2, Propositions 1–3 and Corollary 1, <https://doi.org/10.1371/journal.pone.0182178>, PMCID PMC5568237.
