# Reconstructed trees under protracted speciation are coalescent point processes

**Model.** Starting from one incipient species at time $0$, every species, of either stage, gives birth to new incipient species at rate $b(s)$ at time $s$ (no diversity dependence). A species born at time $s$ stays incipient for a duration $U_s$, then either goes extinct or becomes *good*, and a good species survives a further duration $V_s$ ($V_s = 0$ encodes extinction before becoming good); $U_s$ and $V_s$ may be dependent. In the **constant rate model** $b$ is constant, $U\sim\mathrm{Exp}(\nu_1)$ with $\nu_1 = \lambda_1 + \mu_1$, and independently $V = 0$ with probability $\mu_1/\nu_1$, otherwise $V\sim\mathrm{Exp}(\mu_2)$: incipient species turn good at rate $\lambda_1$ or die at rate $\mu_1$, good species die at rate $\mu_2$.

A **coalescent point process** with stem age $T$ is an ultrametric tree whose tips, ordered left to right, have node depths $H_1, H_2, \dots$ between consecutive tips that are i.i.d. copies of a random variable $H$, stopped at the first value exceeding $T$; the coalescence time of tips $i$ and $i+k$ is $\max(H_{i+1},\dots,H_{i+k})$. With $W(y) = 1/\mathbb P(H > y)$, the likelihood of a reconstructed tree $\tau$ with stem age $T$, $n$ tips and node depths $x_1<\dots<x_{n-1}$ is

$$\mathcal L(\tau) = \frac{C(\tau)}{W(T)}\prod_{i=1}^{n-1}\frac{W'(x_i)}{W(x_i)^2},$$

with $C(\tau) = (n-1)!$ for ranked node depths, or $2^{i(\tau)}$ for the ranked tree shape ($i(\tau)$ the number of internal nodes not subtending cherries).

**Theorem.**

1. Conditional on at least one species extant at $T$, the reconstructed tree of all extant species (incipient or good) is a coalescent point process. Its node-depth law is the law of the depth of an excursion away from $T$ of the process that decreases at slope $-1$ and jumps at rate $b(s)$ at height $s$ by an amount distributed as $U_s + V_s$.
2. In the constant rate model, let $\alpha < \beta$ be the roots of $s^2 + (\mu_2 + \nu_1 - b)s + \nu_1\mu_2 - b\mu_2 - b\lambda_1$; then $\alpha < 0$, and the process is supercritical iff $\beta > 0$. If $\mu_2(\nu_1 - b) - b\lambda_1 \ne 0$ (so $\beta \ne 0$),

$$W(y) = \frac{\mu_2\nu_1}{\alpha\beta} + \frac{b(\alpha + \lambda_1 + \mu_2)}{\alpha(\alpha-\beta)}e^{\alpha y} + \frac{b(\beta + \lambda_1 + \mu_2)}{\beta(\beta-\alpha)}e^{\beta y}.$$

3. Conditional on at least one good species extant at $T$, the reconstructed tree of extant good species is again a coalescent point process; in the constant rate model with $\beta\ne0$ its $W^g$ is

$$W^g(y) = \frac{\mu_2(\nu_1 - b)}{\alpha\beta} + \frac{b\lambda_1\big(\alpha e^{\beta y} - \beta e^{\alpha y}\big)}{\alpha\beta(\beta-\alpha)}, \qquad y \ge 0.$$

The same holds for the tree of *representative* species (one extant descendant per good ancestor, chosen by the ultimogeniture order), with an explicit coalescent distribution.

## Depends on

- [Splits, compatibility, ultrametrics and UPGMA](../../splits-compatibility-ultrametrics-and-upgma/README.md)

## Expansion

Order species by the ultimogeniture order and explore the tree by a contour process that runs down each species' lifetime and jumps up by the total lifetime $U+V$ of each daughter met. This contour is a Lévy-type process with slope $-1$ and jumps at rate $b$; extant species at $T$ correspond to its visits to level $T$, and the depth between consecutive extant species is the depth of the excursion below $T$ between visits. Excursions are i.i.d. by the strong Markov property, which is the coalescent point process property. In the constant rate model, $W$ solves a linear ODE system obtained from the extinction probabilities of incipient and good species; its Laplace transform is a rational function with poles at the roots $\alpha, \beta$ of the quadratic, giving the exponential formula. For good species, restricting to tips that are good preserves the coalescent point process structure, and in the homogeneous model $W^g(y) = W(y) - b\int_0^yW(y-x)\,\mathbb P(U > x)\,dx$.

## Sources

- Amaury Lambert, Hélène Morlon, Rampal S. Etienne, "The reconstructed tree in the lineage-based model of protracted speciation", arXiv (2013). Section 2 (model, ultimogeniture order), Section 4 (coalescent point processes, likelihood, Proposition 4.2), Proposition 5.1, Corollary 5.2, Propositions 6.1–6.4. <https://doi.org/10.48550/arXiv.1301.5512>. Published version: Journal of Mathematical Biology 70(1-2) (2015), 367–397, <https://doi.org/10.1007/s00285-014-0767-x>; locators above refer to the arXiv version.
