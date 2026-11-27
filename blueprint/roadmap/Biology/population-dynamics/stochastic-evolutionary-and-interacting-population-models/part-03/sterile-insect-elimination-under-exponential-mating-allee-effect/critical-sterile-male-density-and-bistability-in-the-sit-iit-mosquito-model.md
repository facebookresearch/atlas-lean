# Critical sterile-male density and bistability in the SIT/IIT mosquito model

**Model.** Let $E$, $M$, $F$ be eggs, fertile wild males and fertile (mated) females, and let $M_i\ge 0$ be a constant density of released sterilizing males with mating competitiveness $\gamma_i>0$:

$$
\begin{aligned}
\frac{dE}{dt} &= bF\Big(1-\frac{E}{K}\Big) - (\nu_E+\mu_E)E,\\
\frac{dM}{dt} &= (1-r)\nu_E E - \mu_M M,\\
\frac{dF}{dt} &= r\nu_E E\,\big(1-e^{-\beta(M+\gamma_i M_i)}\big)\frac{M}{M+\gamma_i M_i} - \mu_F F,
\end{aligned}
$$

with all rates positive and $r\in(0,1)$ the female sex ratio. Define the basic offspring number and the Allee ratio

$$
\mathcal N := \frac{b r\nu_E}{\mu_F(\nu_E+\mu_E)},\qquad \lambda := \frac{\mu_M}{(1-r)\nu_E K},\qquad \psi := \frac{\lambda}{\beta}.
$$

**Theorem.** The system is monotone (cooperative) on the forward-invariant set $\{E\le K\}$, which every trajectory enters in finite time.

1. If $\mathcal N\le 4\psi$ there is no positive steady state, and $(0,0,0)$ is globally asymptotically stable.
2. If $\mathcal N>4\psi$, let $\theta_0\in(0,1)$ solve $1-\theta_0 = -\frac{4\psi}{\mathcal N}\log\theta_0$ and set

$$
M_i^{\mathrm{crit}} := \frac{1}{\gamma_i\beta}\max_{\theta\in[\theta_0,1]}\Big(-\log\theta - \frac{1}{2\psi}\Big(1-\sqrt{1+\frac{4\psi}{\mathcal N}\frac{\log\theta}{1-\theta}}\Big)\Big).
$$

If $M_i^{\mathrm{crit}}>0$, the system has no positive steady state for $M_i>M_i^{\mathrm{crit}}$ (and then $(0,0,0)$ is globally asymptotically stable), exactly one for $M_i=M_i^{\mathrm{crit}}$, and two, $\mathbf E_-\ll\mathbf E_+$, for $0\le M_i<M_i^{\mathrm{crit}}$, with $\mathbf E_-$ unstable and $\mathbf E_+$ locally asymptotically stable. If $\mathcal N\le 1$ then $M_i^{\mathrm{crit}}<0$.
3. *(Bistability.)* For $0\le M_i<M_i^{\mathrm{crit}}$ there is a two-dimensional separatrix $\Sigma\ni\mathbf E_-$, consisting of pairwise order-unrelated points, such that $\mathbb R_+^3=\Sigma_-\cup\Sigma\cup\Sigma_+$, where $\Sigma_-$ (points below $\Sigma$) is the basin of $(0,0,0)$ and $\Sigma_+$ (points above $\Sigma$) is the basin of $\mathbf E_+$. In particular the basin of $(0,0,0)$ contains the order interval $[0,\mathbf E_-)$.

Positive steady states correspond to positive roots $M^*$ of $f(\beta M^*,\beta\gamma_i M_i)=0$ with $f(x,y)=x(1-\psi x)(1-e^{-(x+y)})-(x+y)/\mathcal N$, together with $E^*=K\lambda M^*$ and $F^*=\frac{K(\nu_E+\mu_E)}{b}\frac{\lambda M^*}{1-\lambda M^*}$.

## Expansion

Eliminating $E$ and $F$ at equilibrium reduces the problem to the scalar function $f$; for $M_i=0$ it is concave on $[0,1/\psi]$ with maximum at $Z(\psi)$ given by $e^{-Z}=\psi/(1+\psi-\psi Z)$, and it has two zeros exactly when $\mathcal N$ exceeds $F(\psi)=(1+\psi-\psi Z)/(1-\psi Z)^2$, which behaves like $4\psi$ for large $\psi$. Sterile males shift the second argument of $f$ and lower the curve until the two positive roots merge at $M_i^{\mathrm{crit}}$ (a saddle-node). Because the system is cooperative, the order structure of the equilibria plus their local stability determine all asymptotics (Hirsch–Smith theory), giving the separatrix. A useful approximation, valid when $\beta$ is not small, is $M_i^{\mathrm{crit}}\le \frac{\mathcal N}{4\lambda\gamma_i}(1-1/\mathcal N)^2$, so the sterile-to-wild ratio needed for unconditional elimination is about $(\mathcal N-1)/(4\gamma_i)$.

## Sources

- M. Strugarek, H. Bossin, Y. Dumont, *On the use of the sterile insect technique or the incompatible insect technique to reduce or eliminate mosquito populations*, arXiv:1805.10150 (2018). <https://doi.org/10.48550/arXiv.1805.10150> — Lemmas 2–3 (monotonicity, steady-state count), Propositions 2.3 and 2.4 (global behavior and separatrix), Remarks 2.1–2.2, Appendix A (study of $f$). Published version: Applied Mathematical Modelling 68 (2019), 443–470, <https://doi.org/10.1016/j.apm.2018.11.026>; locators above refer to the arXiv version.
