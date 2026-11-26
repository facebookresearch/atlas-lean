# Incentive stable states under convex mixtures of incentives

**Incentive dynamics.** On the probability simplex, an incentive $\varphi=(\varphi_1,\dots,\varphi_n)$ defines the dynamic

$$
\dot x_i=\varphi_i(x)-x_i\sum_{j=1}^n\varphi_j(x).
$$

The replicator dynamic for a landscape $f$ is the case $\varphi_i(x)=x_if_i(x)$; best-reply, logit and orthogonal-projection dynamics arise from other incentives. A state $\hat x$ is an incentive stable state (ISS) if, for all $x\ne\hat x$ in a neighborhood of $\hat x$,

$$
\sum_i\frac{\hat x_i\,\varphi_i(x)}{x_i}>\sum_i\varphi_i(x).
$$

For the replicator incentive this is the ESS condition $\hat x\cdot f(x)>x\cdot f(x)$. If $\hat x$ is an interior ISS, the Kullback–Leibler divergence $D(\hat x\,\|\,x)=\sum_i\hat x_i\log(\hat x_i/x_i)$ is a local Lyapunov function (Fryer).

**Theorem.** Let $\varphi$ and $\psi$ be incentives and $p\in[0,1]$. Then

1. $\varphi_p=p\varphi+(1-p)\psi$ is an incentive; and
2. if $\hat x$ is an ISS for both $\varphi$ and $\psi$, then $\hat x$ is an ISS for $\varphi_p$, and $D(\hat x\,\|\,x)$ is a local Lyapunov function for the dynamic defined by $\varphi_p$ (when $\hat x$ is interior).

So a population that switches between, for example, replicator and best-reply behavior with probabilities $p$ and $1-p$ keeps a common ESS as a locally stable state. A mixture can also create stability: for the Rock–Scissors–Paper landscape with neutral cycles ($a=b=1$), mixing the replicator incentive with the constant incentive $\psi_i\equiv1$, whose dynamic is $\dot x_i=1-3x_i$, makes the barycenter asymptotically stable for every $p\in(0,1)$.

## Depends on

- [Lyapunov characterization of evolutionarily stable states for the replicator equation](../../population-dynamics/replicator-dynamics/ess-lyapunov-function-for-the-replicator-equation.md)

## Expansion

Both the incentive axioms and the ISS inequality are linear in $\varphi$: multiplying the ISS inequality for $\varphi$ by $p$ and the one for $\psi$ by $1-p$ and adding gives the ISS inequality for $\varphi_p$ on the intersection of the two neighborhoods. Fryer's theorem then gives the KL Lyapunov function. When one incentive has a different global Lyapunov function, the same averaging applies to Lyapunov functions: for the replicator and projection incentives with a common interior ESS, $V=pD(\hat x\,\|\,x)+\tfrac{1-p}{2}\|\hat x-x\|^2$ decreases along the mixed dynamic.

## Sources

- Marc Harper, Dashiell Fryer and Andrew Vlasic, *Mean evolutionary dynamics for stochastically switching environments*, arXiv:1306.2373 (2013), Theorem 2 and Section 5. <https://doi.org/10.48550/arXiv.1306.2373>
