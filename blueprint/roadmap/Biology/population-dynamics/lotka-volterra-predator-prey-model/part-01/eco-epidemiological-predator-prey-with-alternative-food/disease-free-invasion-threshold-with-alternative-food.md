# Disease-free invasion threshold with alternative food

Consider susceptible prey $s$, infected prey $i$ and predators $p$ in the nondimensional system

$$\dot s = s(1-s) - \gamma i s - \frac{a s p}{1 + \alpha\xi + b s}, \qquad \dot i = \gamma i s - \frac{\beta i p}{1 + \alpha\xi} - d i,$$

$$\dot p = \frac{\epsilon(s + c\xi)p}{1 + \alpha\xi + b s} + \frac{\eta i p}{1 + \alpha\xi} - e p,$$

with all parameters positive. Here $\gamma$ is the infection rate, predation on susceptibles is Holling type II and on infected prey mass action, $\xi$ is proportional to the biomass of a constant alternative food, and $\alpha$ is the ratio of handling times of alternative food and prey (low $\alpha$ = high-quality food) (Sahoo and Poria 2013, system (2)).

**Facts.**

1. If $e > \epsilon c\xi$, $a \ge \epsilon$ and $\beta \ge \eta$, all solutions starting in $\mathbb{R}^3_+$ are uniformly bounded, with $\limsup_{t\to\infty}(s+i+p) \le 1/\theta$, $\theta = \min\{1, d, e - \epsilon c\xi\}$. The source's Theorem 1 prints boundedness for all positive parameters, but its proof needs $\theta > 0$ and drops the terms $-(a-\epsilon)sp/(1+\alpha\xi+bs)$ and $-(\beta-\eta)ip/(1+\alpha\xi)$, which requires $a \ge \epsilon$ and $\beta \ge \eta$; the page states the corrected form, which follows line by line from the theorem's own estimate. Without these conditions the claim fails: the face $s = i = 0$ is invariant, and on it $\dot p = p\bigl(\epsilon c\xi/(1+\alpha\xi) - e\bigr)$ grows exponentially when $\epsilon c\xi > e(1+\alpha\xi)$.
2. The trivial equilibrium $(0,0,0)$ is always unstable, and the axial equilibrium $(1,0,0)$ is unstable if $\gamma > d$ (disease can invade the predator-free prey population) or $e < \epsilon(1 + c\xi)/(1 + \alpha\xi + b)$ (predators can invade) (Theorem 2).
3. At a disease-free equilibrium $E_D = (\bar s, 0, \bar p)$ the Jacobian has $a_{21} = a_{23} = 0$, so one eigenvalue is

$$a_{22} = \gamma \bar s - \frac{\beta \bar p}{1 + \alpha\xi} - d,$$

and $E_D$ is locally stable if $a_{22} < 0$ and the remaining $(s,p)$ block satisfies the Routh–Hurwitz conditions, and unstable if $a_{22} > 0$; at $a_{22} = 0$ the linearization does not decide. (The source's Theorem 3 gives the sufficient direction only: $E_D$ "is locally stable if the following conditions hold: $\Theta_1>0$, $\Theta_3>0$ and $\Theta_1\Theta_2-\Theta_3>0$".)

Condition 3 shows the mechanism of control: alternative food changes $(\bar s, \bar p)$ and the effective predation pressure $\beta/(1+\alpha\xi)$ on infected prey, so that $\gamma\bar s < d + \beta\bar p/(1+\alpha\xi)$ can hold at infection rates where it fails without alternative food; numerically there is a critical infection rate above which the system cannot become disease-free without alternative food but can with it.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)

## Expansion

Under the hypotheses of Fact 1, boundedness follows from the linear differential inequality $\dot w + \theta w \le 1$ for $w = s + i + p$. At $E_T$ the eigenvalues are $1$, $-d$ and $\epsilon c\xi/(1+\alpha\xi) - e$; at $E_A$ they are $-1$, $\gamma - d$ and $\epsilon(1+c\xi)/(1+\alpha\xi+b) - e$. At $E_D$ the infected equation decouples to first order because $\dot i$ is proportional to $i$, giving the separable eigenvalue $a_{22}$, which is the per-capita growth rate of a rare infection.

## Sources

- B. Sahoo and S. Poria, *Disease control in a food chain model supplying alternative food*, Applied Mathematical Modelling 37(8) (2013), 5653–5663, system (2) and Theorems 1–3. <https://doi.org/10.1016/j.apm.2012.11.017> (PMCID: PMC7117010)
