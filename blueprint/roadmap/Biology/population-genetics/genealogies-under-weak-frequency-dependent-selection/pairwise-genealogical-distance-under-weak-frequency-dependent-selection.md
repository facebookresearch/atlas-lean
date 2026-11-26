# Pairwise genealogical distance under weak frequency-dependent selection

**Model.** A continuous-time Moran model of $N$ haploid individuals of types (strategies) $A$ and $B$, whose type-$A$ frequency converges as $N \to \infty$ to the Wright–Fisher diffusion with linear frequency-dependent selection

$$dX = \big((1-X)\theta_A - X\theta_B\big)\,dt + \alpha X(1-X)(\beta - \gamma X)\,dt + \sqrt{X(1-X)}\,dW,$$

with scaled selection coefficient $\alpha \ge 0$, payoff parameters $\beta, \gamma \in \mathbb R$ (the fitness advantage of $A$ at frequency $x$ is proportional to $\beta - \gamma x$, as for a $2 \times 2$ game), and mutation rates $\theta_A, \theta_B > 0$. In the particle model, every pair resamples at rate $1$ (neutral reproduction), selective events at rates $\alpha|\beta|$ and $\alpha|\gamma|$ implement the linear and the frequency-dependent part of selection (the latter by an individual checking the type of a randomly chosen individual before reproducing), and each individual mutates at rate $\bar\theta = \theta_A + \theta_B$ to type $A$ with probability $\theta_A/\bar\theta$ and to $B$ otherwise.

Let $\mathbf E_{N,\alpha}$ denote expectation under the stationary law of this Moran model and $R_{12}$ the genealogical distance (time back to the most recent common ancestor) of two individuals sampled from the stationary population. Under neutrality $R_{12}$ is asymptotically exponential with mean $1$, so $\mathbf E_{N,0}[e^{-\lambda R_{12}}] \to 1/(1+\lambda)$.

**Theorem.** For $\lambda \ge 0$, as $N \to \infty$,

$$\lim_{N\to\infty}\mathbf E_{N,\alpha}\big[e^{-\lambda R_{12}}\big] = \frac{1}{1+\lambda} - \alpha\gamma\,\frac{\theta_A\theta_B}{\bar\theta}\,\frac{(2+\bar\theta+\lambda)\,\lambda}{(6+\bar\theta+\lambda)(3+\bar\theta+\lambda)(1+\bar\theta+\lambda)(1+\bar\theta)(1+\lambda)^2} + O(\alpha^2),$$

and in particular

$$\lim_{N\to\infty}\mathbf E_{N,\alpha}[R_{12}] = 1 + \alpha\gamma\,\frac{\theta_A\theta_B}{\bar\theta}\,\frac{2+\bar\theta}{(6+\bar\theta)(3+\bar\theta)(1+\bar\theta)^2} + O(\alpha^2).$$

To first order in $\alpha$ the linear (frequency-independent) part $\beta$ of selection leaves pairwise genealogical distances unchanged; only the frequency-dependent part $\gamma$ acts. Stabilizing frequency dependence ($\gamma > 0$, which pushes frequencies toward an interior equilibrium) lengthens genealogies, as balancing selection does, and $\gamma < 0$ shortens them.

## Expansion

The proof uses an ancestral selection graph adapted to frequency-dependent selection: backward in time, the two sampled lines coalesce at rate $1$, branch at selective events, and frequency-dependent events create a branching with an additional checking line; mutation events, read backward, fix the type of a line and so cut its dependence on the past. Expanding the stationary law in $\alpha$, the first-order term involves only configurations with one selective branching; the term coming from $\beta$-branchings vanishes in the first-order expansion of the Laplace transform, while the $\gamma$-branchings, which need three lines of types to be compared, produce the rational function with the factors $(1+\bar\theta+\lambda)$, $(3+\bar\theta+\lambda)$ and $(6+\bar\theta+\lambda)$, the total event rates with $2$, $3$ and $4$ lines. Setting $\theta_A = \theta_B = 0$ in the same graph yields a genealogical proof of the one-third rule for fixation probabilities.

## Depends on

- [The one-third rule for weak selection in the Moran process](../../population-genetics/moran-model/one-third-rule-under-weak-selection.md)

## Sources

- Peter Pfaffelhuber, Benedikt Vogt, "Finite populations with frequency-dependent selection: a genealogical approach", arXiv (2012). Section 2 (model, Equation for the diffusion and Moran transition rules 1–4), Theorem 1 (one-third rule), Theorem 2, Section 6. <https://doi.org/10.48550/arXiv.1207.6721>
