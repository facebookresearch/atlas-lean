# Langevin Monte Carlo

Langevin Monte Carlo (the unadjusted Langevin algorithm) samples approximately from a density $\pi \propto e^{-f}$ on $\mathbb{R}^p$ by gradient descent plus Gaussian noise, $\vartheta_{k+1} = \vartheta_k - h \nabla f(\vartheta_k) + \sqrt{2h}\,\xi_{k+1}$. It is the Euler discretization of the Langevin diffusion $dL_t = -\nabla f(L_t)\,dt + \sqrt 2\, dW_t$, whose law is the Wasserstein gradient flow of the relative entropy $\mathrm{KL}(\cdot \,\|\, \pi)$ (Jordan, Kinderlehrer and Otto). In this view sampling is optimization over probability measures: for a strongly log-concave target the iterates contract in $W_2$ at the gradient-descent rate $1 - mh$, up to a discretization bias of order $\sqrt{hp}$ (Dalalyan; Durmus and Moulines), and convergence in relative entropy follows the same gradient-flow analysis (Cheng and Bartlett).

- [The Langevin Monte Carlo update map is measurable](measurable-lmc-update.md)
- [One step of the Langevin Monte Carlo algorithm, on laws](lmc-step.md)
- [One Langevin Monte Carlo step from a point is Gaussian](lmc-step-dirac.md)
- [Wasserstein convergence of Langevin Monte Carlo (Dalalyan)](wasserstein-lmc-le.md)

## Related topics

- [Markov chain Monte Carlo](../markov-chain-monte-carlo/README.md): exact-invariance samplers (Metropolis–Hastings, Gibbs) on finite spaces; Langevin Monte Carlo has no accept/reject step, so its invariant law is only close to the target.
- [Wasserstein gradient flows and the JKO scheme](../../../../MeasureTheory/optimal-transport/wasserstein-gradient-flows-and-the-jko-scheme/README.md): the Langevin diffusion as the $W_2$ gradient flow of the free energy.
- [Transport-cost inequalities](../../../../Probability/concentration-inequalities/transport-cost-inequalities/README.md): the log-Sobolev and Talagrand inequalities that give exponential convergence of the diffusion in relative entropy and in $W_2$.
- [Accelerated gradient methods](../../../../Analysis/convex-analysis-and-variations/accelerated-gradient-methods/README.md): the optimization side of the same continuous-time view of algorithms.
- [Ornstein–Uhlenbeck process](../../../../Probability/stochastic-calculus/ornstein-uhlenbeck-process/README.md): the Langevin diffusion for a quadratic potential, the Gaussian case in which the target of the algorithm is a Gaussian.
- [Fokker–Planck equation](../../../../Probability/stochastic-calculus/fokker-planck-equation/README.md): the equation of the law of the Langevin diffusion, whose free energy decreases along the flow.
