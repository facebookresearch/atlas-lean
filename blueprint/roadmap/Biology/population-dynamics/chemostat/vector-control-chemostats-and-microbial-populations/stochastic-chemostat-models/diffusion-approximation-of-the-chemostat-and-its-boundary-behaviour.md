# Diffusion approximation of the chemostat and its boundary behaviour

For the chemostat with biomass $\beta$, substrate $\sigma$, dilution rate $D$, feed concentration $s^{\rm in}$, yield coefficient $k$, specific growth rate $\mu$ (bounded, non-negative, $\mu(0)=0$, extended by $\mu(\sigma)=0$ for $\sigma\le0$) and flux scale parameters $K_1,\dots,K_5$ (biomass growth, substrate consumption, inflow, biomass outflow, substrate outflow), the diffusion approximation of the five-mechanism jump model is

$$d\beta_t=[\mu(\sigma_t)-D]\,\beta_t\,dt+\sqrt{\frac{\mu(\sigma_t)\beta_t}{K_1}+\frac{D\beta_t}{K_4}}\;dW^b_t,$$

$$d\sigma_t=\big[-k\mu(\sigma_t)\beta_t+D(s^{\rm in}-\sigma_t)\big]\,dt+\sqrt{\frac{k\mu(\sigma_t)\beta_t}{K_2}+\frac{Ds^{\rm in}}{K_3}+\frac{D\sigma_t}{K_5}}\;dW^s_t,$$

with independent Brownian motions $W^b,W^s$; its Euler–Maruyama discretization is the Gaussian (normal) approximation of the jump process, and as all $K_i\to\infty$ it converges to the deterministic chemostat.

**Statement.**
1. *Well-posedness.* The system has a pathwise unique strong solution defined for all $t\ge0$, taking values in $\mathcal{D}=[0,\infty)\times[-\tfrac{K_5}{K_3}s^{\rm in},\infty)$.
2. *Washout is absorbing.* $\beta_t\ge0$ for all $t$, and $\beta=0$ is absorbing.
3. *Substrate after washout.* On $\{\beta=0\}$ the substrate follows the Cox–Ingersoll–Ross-type equation $d\sigma_t=D(s^{\rm in}-\sigma_t)\,dt+\sqrt{Ds^{\rm in}/K_3+D\sigma_t/K_5}\;dW^s_t$, and
   - if $s^{\rm in}\big(\frac{1}{K_3}+\frac{1}{K_5}\big)\ge\frac{1}{2K_5^2}$, then $\sigma_t$ never reaches $-\frac{K_5}{K_3}s^{\rm in}$;
   - if $s^{\rm in}\big(\frac{1}{K_3}+\frac{1}{K_5}\big)<\frac{1}{2K_5^2}$, then $\sigma_t$ reaches $-\frac{K_5}{K_3}s^{\rm in}$ in finite time and is reflected.

Negative substrate values are an artefact of the Gaussian approximation; the diffusion model is meaningful at large concentrations, and the jump model should be used near the axes.

## Expansion

The diffusion is obtained from the jump generator by a second-order Taylor expansion of each difference operator (one Brownian motion per mechanism, then merged by summing variances). Existence and uniqueness use localization: the coefficients are Lipschitz on $\mathcal{D}_N=[\frac1N,N]\times[-\frac{K_5}{K_3}s^{\rm in}+\frac1N,N]$, giving consistent strong solutions up to exit times, and the solution cannot cross $\partial\mathcal{D}$, so the exit times tend to infinity. The boundary classification applies Itô's formula to $\tilde\sigma=Ds^{\rm in}/K_3+D\sigma/K_5$, which is a CIR process $d\tilde\sigma=(a+b\tilde\sigma)dt+c\sqrt{\tilde\sigma}\,dW$, and uses Feller's criterion: $0$ is not reached iff $a\ge c^2/2$.

## Depends on

- [Five-mechanism pure jump chemostat and its fluid limit](five-mechanism-pure-jump-chemostat-and-its-fluid-limit.md)

## Proof depends on

- [Itô's formula for Itô processes with locally integrable coefficients](../../../../../Probability/stochastic-calculus/it-s-formula/ito-formula-for-ito-processes-time-dependent-loc.md)

## Sources

- F. Campillo, M. Joannides and I. Larramendy-Valverde, *Stochastic models of the chemostat*, arXiv:1011.5108 (2010), <https://doi.org/10.48550/arXiv.1011.5108>. Section "Models at different scales", subsection "Diffusion model" (SDE, remark on the Cox–Ingersoll–Ross model, behaviour near the axes); appendix "Existence and uniqueness for a solution of the SDE".
