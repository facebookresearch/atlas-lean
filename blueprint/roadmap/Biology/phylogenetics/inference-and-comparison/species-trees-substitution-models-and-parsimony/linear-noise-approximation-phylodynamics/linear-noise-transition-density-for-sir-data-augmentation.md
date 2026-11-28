# Linear noise transition density for SIR data augmentation

Write the SIR Markov jump process with state $X = (S, I)$, effect matrix $A$ (rows $(-1, 1)$ for infection and $(0,-1)$ for removal), rate vector $h(X,\theta) = (\beta S I, \gamma I)^{\top}$ and $H = \mathrm{diag}(h)$. On a grid $t_0 < t_1 < \dots < t_T$ with rates $\theta_{i-1}$ constant on $[t_{i-1}, t_i)$, the linear noise approximation represents $X_i = \eta(t_i) + M(t_i)$, where

$$ \frac{d\eta}{dt} = A^{\top} h(\eta, \theta_{i-1}), \qquad dM = F(\eta,\theta_{i-1})\, M\, dt + \sqrt{A^{\top} H(\eta, \theta_{i-1}) A}\; dW_t , $$

and $F = \partial (A^{\top} h)/\partial X$ evaluated at $\eta$. Then $M$ is Gaussian with mean $m$ and covariance $\Phi$ solving

$$ \frac{dm}{dt} = F m, \qquad \frac{d\Phi}{dt} = F\Phi + \Phi F^{\top} + A^{\top} H A . $$

In the non-restarting scheme, $\eta$ is propagated continuously across intervals, while $m(t_{i-1}) = X_{i-1} - \eta(t_{i-1})$ and $\Phi(t_{i-1}) = 0$. This gives the Gaussian transition density

$$ X_i \mid X_{i-1} \sim \mathcal{N}\big(\eta(t_i) + m(t_i),\ \Phi(t_i)\big) , $$

which replaces the intractable jump-process transition in the posterior

$$ \Pr(X_{0:T}, \theta_{0:T} \mid \mathbf{g}) \propto \Pr(\mathbf{g} \mid X_{0:T}, \theta_{0:T}) \prod_{i=1}^{T} \Pr(X_i \mid X_{i-1}, \theta_{i-1})\, \Pr(\theta_{0:T})\, \Pr(X_0) . $$

## Depends on

- [SIR structured coalescent likelihood for serially sampled genealogies](sir-structured-coalescent-likelihood-for-serially-sampled-genealogies.md)

## Expansion

The jump process is first approximated by the chemical Langevin SDE $dX = A^{\top}h\,dt + \sqrt{A^{\top}HA}\,dW$; linearizing it around the deterministic ODE solution $\eta$ gives a linear SDE for the fluctuation $M$, whose solution is Gaussian with moments given by the two linear ODEs. Because $m$ obeys a linear ODE it can be written with the fundamental matrix of $F$, which allows a non-centered reparameterization of the latent trajectory by standard normal variables; the latent trajectory is then updated by elliptical slice sampling together with the time-varying rates. The same construction applies to any density-dependent reaction network specified by an effect matrix and a rate vector.

## Sources

- Mingwei Tang, Gytis Dudas, Trevor Bedford, Vladimir N. Minin, "Fitting stochastic epidemic models to gene genealogies using linear noise approximation", The Annals of Applied Statistics 17 (2023), 1–22, <https://doi.org/10.1214/21-aoas1583>. Published version of arXiv:1902.08877, cited next; locators there refer to the arXiv version.
- M. Tang, G. Dudas, T. Bedford, V. N. Minin, "Fitting stochastic epidemic models to gene genealogies using linear noise approximation", arXiv:1902.08877 (2019), Section 2.2 (Bayesian data augmentation; posterior and linear noise approximation with non-restarting initial conditions), Section 2.3 (reparameterization and MCMC), and the appendix sections on the derivation of the linear noise approximation and the non-centered parameterization. <https://doi.org/10.48550/arXiv.1902.08877>
