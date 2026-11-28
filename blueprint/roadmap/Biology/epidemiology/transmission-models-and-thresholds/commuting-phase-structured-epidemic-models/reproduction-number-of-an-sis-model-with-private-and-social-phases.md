# Reproduction number of an SIS model with private and social phases

**Model.** A community of constant size $N$ has non-commuters, fraction $1 - p$, who always stay in the **private phase** (their residential district), and commuters, fraction $p \in (0,1)$, who alternate between the private phase and a **social phase** at a central place. Write $(\bar S, \bar I)$ for non-commuters, $(S, I)$ for commuters in the private phase and $(\tilde S, \tilde I)$ for commuters in the social phase. Commuters switch private $\to$ social at rate $m_{rc}$ and social $\to$ private at rate $m_{cr}$ (separately for susceptibles and infectives), with one-day cycles $1/m_{rc} + 1/m_{cr} = 1$, so $\tau = 1/m_{cr} \in (0,1)$ is the daily fraction of time in the social phase. Infection forces are $\Lambda$ in the private phase (complete mixing of non-commuters and private-phase commuters) and $\tilde\Lambda$ in the social phase; recovery at rate $\rho < 1$ per day happens only in the private phase, and recovered individuals are susceptible again:

$$\begin{aligned}
\dot{\bar S} &= -\Lambda \bar S + \rho \bar I, & \dot{\bar I} &= \Lambda \bar S - \rho \bar I,\\
\dot S &= -\Lambda S + \rho I - m^S_{rc} S + m^S_{cr}\tilde S, & \dot I &= \Lambda S - \rho I - m^I_{rc} I + m^I_{cr}\tilde I,\\
\dot{\tilde S} &= -\tilde\Lambda \tilde S + m^S_{rc} S - m^S_{cr}\tilde S, & \dot{\tilde I} &= \tilde\Lambda \tilde S + m^I_{rc} I - m^I_{cr}\tilde I .
\end{aligned}$$

At the disease-free equilibrium $\bar S_0^* = (1-p)N$, $S_0^* = (1 - \tau_S)pN$, $\tilde S_0^* = \tau_S pN$. Let $\lambda_0^*$ and $\tilde\lambda_0^*$ be the derivatives of $\Lambda$ and $\tilde\Lambda$ with respect to infectives there ($\beta\kappa$ and $\beta K$ for mass-action incidence with contact coefficients $\kappa$, $K$; $\beta\omega/(\bar S_0^* + S_0^*)$ and $\beta\Omega/\tilde S_0^*$ for ratio-dependent incidence).

**Theorem.** With

$$a = \frac{\lambda_0^*(\bar S_0^* + S_0^*)}{\rho},\qquad d = \frac{\rho + m^I_{rc}}{\rho}\cdot\frac{\tilde\lambda_0^*\tilde S_0^*}{m^I_{cr}},\qquad e = \frac{m^I_{rc}}{\rho}\cdot\frac{\lambda_0^* S_0^*}{\rho}\cdot\frac{\tilde\lambda_0^*\tilde S_0^*}{m^I_{cr}},$$

the basic reproduction number is

$$\mathcal{R}_0 = \tfrac12\Big(a + d + \sqrt{(a - d)^2 + 4e}\Big),$$

and $\mathcal{R}_0 < 1$ if and only if $a < 1$, $d < 1$ and $(1 - a)(1 - d) > e$.

For mass-action incidence in both phases, $\mathcal{R}_0$ as a function of the commuter ratio $p$ has an interior minimum $p^* \in (0,1)$ exactly under an explicit condition on the ratio $K/\kappa$ of social to private contact coefficients and the durations $\tau_S, \tau_I, \rho$; otherwise it is monotone, and its maximum over $p \in [0,1]$ is attained at $p = 0$ or $p = 1$. With mass-action private and ratio-dependent social incidence, $\mathcal{R}_0$ is monotone in $p$.

## Expansion

The infected compartments are private-phase infectives (non-commuters and commuters, which mix completely and can be pooled at the threshold) and social-phase infectives, so the next-generation matrix is $2 \times 2$ and $\mathcal{R}_0$ is its Perron root; the threshold conditions are the usual ones for a nonnegative $2\times 2$ matrix to have spectral radius below one. Commuting has competing effects: it removes people from the private pool but concentrates them in a social pool whose contact rate scales with its own density under mass action. When social contacts are intense relative to private ones, moving some but not all of the population into commuting dilutes transmission in both places, which is why an intermediate commuter ratio can minimize the risk of spread, independently of $\beta$ and $N$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- H. Seno, "An SIS model for the epidemic dynamics with two phases of the human day-to-day activity", Journal of Mathematical Biology (2020), model (3) with constraints (4)–(5), infection forces (6)–(10), disease-free equilibrium (12), reproduction number (13), Theorems 1–4 and Corollaries 1–2, <https://doi.org/10.1007/s00285-020-01491-0>, PMCID PMC7139907.
