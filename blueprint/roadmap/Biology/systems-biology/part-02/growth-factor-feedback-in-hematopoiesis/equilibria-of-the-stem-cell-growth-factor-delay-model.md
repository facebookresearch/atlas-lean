# Equilibria of the stem cell–growth factor delay model of hematopoiesis

Let $Q(t)$ be the quiescent hematopoietic stem cell population, $M(t)$ the circulating mature blood cell population and $E(t)$ the growth factor concentration. Proliferating stem cells divide after a cell-cycle duration $\tau>0$ and die by apoptosis at rate $\gamma\ge 0$ during the cycle. The model is the delay system

$$
\begin{aligned}
Q'(t) &= -\delta Q(t) - g(Q(t)) - \beta(Q(t),E(t))\,Q(t) + 2e^{-\gamma\tau}\beta(Q(t-\tau),E(t-\tau))\,Q(t-\tau),\\
M'(t) &= -\mu M(t) + g(Q(t)),\\
E'(t) &= -kE(t) + f(M(t)),
\end{aligned}
$$

with the hypotheses:

- $\delta\ge 0$ (death of quiescent cells), $\mu>0$ (clearance of mature cells), $k>0$ (degradation of growth factor);
- the differentiation flux $g$ is $C^1$, nonnegative, $g(0)=0$, and $Q\mapsto g(Q)/Q$ is nondecreasing, so that $0\le g'(0)\le g(Q)/Q\le g'(Q)$ for $Q>0$; moreover $g(Q)>0$ for $Q>0$ (for instance if $g'(0)>0$); with $g(Q)/Q$ nondecreasing this gives $g(Q)\to+\infty$ as $Q\to\infty$, $M^*>0$ and $g'(Q^*)\ge g(Q^*)/Q^*>0$ at a positive root $Q^*$. The source derives $g\to\infty$ from the monotonicity of $g(Q)/Q$ alone, which fails when $g$ vanishes on an interval $[0,a]$ (then $M^*=g(Q^*)/\mu$ can be $0$ and no positive steady state exists although the condition of item 2 holds), so the page assumes positivity of $g$;
- the feedback $f$ is $C^1$, positive and decreasing, with $f(M)\to 0$ as $M\to\infty$;
- the reintroduction rate $\beta(Q,E)$ is $C^1$, increasing in $E$ with $\beta(Q,0)=0$, and decreasing in $Q$;
- the source's standing assumption (6): $\lim_{Q\to\infty}\beta\big(Q,\tfrac1kf(\tfrac1\mu g(Q))\big)=0$.

**Boundedness.** Solutions with nonnegative initial history stay nonnegative. If moreover $\lim_{Q\to\infty}\beta(Q,E)=0$ for every $E\ge0$ and $\delta+g'(0)>0$, then all solutions are bounded.

**Steady states.** Write $\beta_0:=\beta(0,f(0)/k)$.

1. If $\delta+g'(0)>(2e^{-\gamma\tau}-1)\beta_0$, the only steady state is the trivial one $(0,0,f(0)/k)$ (extinction of the stem cells with saturated growth factor).
2. If $\delta+g'(0)<(2e^{-\gamma\tau}-1)\beta_0$, there are exactly two steady states: the trivial one and a unique positive one $(Q^*,M^*,E^*)$, where $Q^*$ is the unique positive root of

$$
\left(2e^{-\gamma\tau}-1\right)\beta\!\left(Q,\tfrac{1}{k}f\!\left(\tfrac{1}{\mu}g(Q)\right)\right)=\delta+\frac{g(Q)}{Q},
$$

and $M^*=g(Q^*)/\mu$, $E^*=f(M^*)/k$. Equivalently, for $\gamma>0$, the positive steady state exists if and only if $\delta+g'(0)<\beta_0$ and

$$
0\le\tau<\tau_{\max}:=\frac{1}{\gamma}\ln\!\left(\frac{2\beta_0}{\delta+g'(0)+\beta_0}\right).
$$

In particular, for $\gamma>0$ a positive steady state requires $\tau<\ln 2/\gamma$. For $\gamma=0$ it exists for every $\tau\ge0$ if and only if $\delta+g'(0)<\beta_0$ (that is, $\tau_{\max}=+\infty$).

**Stability of the trivial state.** Under condition 1 the trivial steady state is locally asymptotically stable for every $\tau\ge0$; under condition 2 it is unstable for every $\tau\ge0$. The system thus undergoes a transcritical bifurcation at $\delta+g'(0)=(2e^{-\gamma\tau}-1)\beta_0$.

## Expansion

The proliferating compartment decouples, so the dynamics reduce to $(Q,M,E)$. At a positive equilibrium, $M$ and $E$ are slaved to $Q$, so $Q^*$ solves $(2e^{-\gamma\tau}-1)\widetilde\beta(Q)=\delta+g(Q)/Q$ with $\widetilde\beta(Q)=\beta(Q,f(g(Q)/\mu)/k)$. Because $\beta$ decreases in $Q$, increases in $E$, $f$ decreases and $g$ increases, $\widetilde\beta$ is strictly decreasing from $\beta_0$ to $0$, while $\delta+g(Q)/Q$ is nondecreasing from $\delta+g'(0)$; the two curves cross exactly once iff the stated inequality holds. Linearising at the trivial state gives a scalar characteristic equation $\lambda+A-Be^{-\lambda\tau}=0$ with $A>0$; the classical Hayes criterion for this equation gives stability for all $\tau$ when $A>B$ and a nonnegative real root for all $\tau$ when $A<B$. By the implicit function theorem $Q^*$ and $M^*$ decrease and $E^*$ increases with $\tau$, and the positive equilibrium merges with the trivial one as $\tau\to\tau_{\max}$.

## Sources

- M. Adimy, F. Crauste, S. Ruan, "Modelling hematopoiesis mediated by growth factors with applications to periodic hematological diseases", Section 2 (Propositions 2.1 and 2.2) and Section 3 (Proposition 3.1). <https://doi.org/10.48550/arXiv.0904.2501>
