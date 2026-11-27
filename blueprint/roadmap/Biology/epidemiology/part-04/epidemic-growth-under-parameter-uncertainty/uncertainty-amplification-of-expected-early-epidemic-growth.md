# Uncertainty amplification of expected early epidemic growth

**Setting.** In the SIR model $S' = -\beta(z) S I$, $I' = \beta(z) S I - \gamma I$, let the contact rate be random, $\beta(z) = \beta + \alpha z$ with $\alpha > 0$ and $z$ a real random variable with density $p(z)$, while $S(0) = S_0$, $I(0) = I_0$ and $\gamma$ are deterministic. During the initial exponential phase $S \approx S_0$, so

$$I(z, t) = I_0\, e^{((\beta + \alpha z) S_0 - \gamma)\, t}.$$

**Proposition.**

1. The expected prevalence is the deterministic exponential corrected by the moment generating function of $z$:

$$\mathbb{E}[I(\cdot, t)] = I_0\, e^{(\beta S_0 - \gamma)t}\, W(t), \qquad W(t) = \mathbb{E}\big[e^{\alpha z S_0 t}\big].$$

2. If $\mathbb{E}[z] = 0$ and $z$ is not almost surely constant, then $W(t) > 1$ for all $t > 0$: uncertainty in the contact rate amplifies expected early growth beyond that of the mean model. For $z$ uniform on $[-1, 1]$,

$$W(t) = \frac{\sinh(\alpha S_0 t)}{\alpha S_0 t}.$$

3. Uncertainty in the initial data alone, $I(z, 0) = I_0 + \mu z$ with $\beta$ deterministic, has no such effect: $\mathbb{E}[I(\cdot, t)] = (I_0 + \mu\bar z) e^{(\beta S_0 - \gamma)t}$ with $\bar z = \mathbb{E}[z]$.
4. For a discrete random input taking values $z_k$ with probabilities $p_k$, the expected SIR trajectory $\bar S, \bar I = \sum_k p_k I_k, \bar R$ satisfies a multi-compartment system with infected subclasses $p_k I_k$, transmission rates $\tilde\beta_k = S_k\beta_k/\bar S$ and recovery rates $\gamma_k$; with two values it has the form of a detected/undetected infection model.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Item 1 is linearity of expectation applied to the explicit exponential. For item 2, $x \mapsto e^{\alpha S_0 t x}$ is strictly convex, so Jensen's inequality gives $W(t) > e^{\alpha S_0 t\, \mathbb{E}[z]} = 1$; the uniform case is $\frac12\int_{-1}^{1} e^{c z}\, dz = \sinh(c)/c$ with $c = \alpha S_0 t$. Item 3 is linear in $z$, so only the mean enters. Item 4 follows by writing each realization's SIR equations, multiplying by $p_k$ and summing, and absorbing the realization-dependent susceptible fractions into the rates $\tilde\beta_k$.

## Sources

- G. Albi, L. Pareschi, M. Zanella, "Control with uncertain data of socially structured compartmental epidemic models", *Journal of Mathematical Biology* 82 (2021) 63, section "Socially structured models with uncertain inputs", Eqs. (17)–(22) and Remark 1 (the amplification observation is attributed there to Roberts 2013). <https://doi.org/10.1007/s00285-021-01617-y> (PMC8141280).
