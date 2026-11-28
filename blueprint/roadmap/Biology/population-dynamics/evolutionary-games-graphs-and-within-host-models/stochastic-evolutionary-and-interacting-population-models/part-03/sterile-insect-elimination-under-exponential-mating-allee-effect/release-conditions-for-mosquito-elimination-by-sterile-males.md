# Release conditions for mosquito elimination by sterile males

**Model with releases.** In the egg–male–female model with mate-finding Allee effect, let the sterile male density obey $\dot M_i = u(t) - \mu_i M_i$ with release rate $u(t)\ge 0$:

$$
\begin{aligned}
\frac{dE}{dt} &= bF\Big(1-\frac{E}{K}\Big) - (\nu_E+\mu_E)E, &\qquad \frac{dM}{dt} &= (1-r)\nu_E E - \mu_M M,\\
\frac{dM_i}{dt} &= u(t) - \mu_i M_i, &\qquad \frac{dF}{dt} &= r\nu_E E\big(1-e^{-\beta(M+\gamma_i M_i)}\big)\frac{M}{M+\gamma_i M_i} - \mu_F F.
\end{aligned}
$$

Let $M_i^{\mathrm{crit}}$ be the critical constant sterile density above which the system with constant $M_i$ has no positive steady state, and assume $M_i^{\mathrm{crit}}>0$, so that the system without releases ($M_i=0$) is bistable with wild equilibrium $\mathbf E_+(M_i=0)$ and with $\Sigma_-(M_i=0)$ the basin of $(0,0,0)$ (notation of the page this one depends on). For a constant density $M_i>M_i^{\mathrm{crit}}$, let $(E,M,F)$ solve the system with that constant $M_i$, started at $(E,M,F)(0)=\mathbf E_+(M_i=0)$, and let

$$
\tau(M_i) := \inf\{t\ge 0 : (E,M,F)(t)\in\Sigma_-(M_i=0)\}
$$

be the first time at which it enters the basin of extinction of the system without releases.

**Theorem.**

1. *(Constant releases.)* If $u\equiv u_0>\mu_i M_i^{\mathrm{crit}}$, the extinction state is globally asymptotically stable. If $u_0<\mu_i M_i^{\mathrm{crit}}$, the state space splits into open basins of extinction and of a positive equilibrium, separated by a separatrix.
2. *(Periodic releases.)* For an $\omega$-periodic release profile, $M_i$ converges to a periodic profile $M_i^{\mathrm{per}}$ with minimum $\underline M_i$ and maximum $\overline M_i$. If $\underline M_i>M_i^{\mathrm{crit}}$ the limiting periodic system has extinction globally asymptotically stable; if $\overline M_i<M_i^{\mathrm{crit}}$ it has at least one positive periodic orbit. With $\underline M_i>M_i^{\mathrm{crit}}$, stopping after $n$ periods still yields extinction as soon as $n\ge \tau(\underline M_i)/\omega$.
3. *(Impulsive releases.)* For impulses $M_i(nT^+)=M_i(nT)+\Lambda$ every period $T$, the sterile density converges to $M_i^{\mathrm{imp}}(t)=\Lambda e^{-\mu_i(t-\lfloor t/T\rfloor T)}/(1-e^{-\mu_i T})$, with minimum $\underline M_i^{\mathrm{imp}}=\Lambda e^{-\mu_i T}/(1-e^{-\mu_i T})$. Let

$$
\mathcal S := \frac{(1-r)\nu_E\,\mathcal N}{4\mu_M\gamma_i}\Big(1-\frac{1}{\mathcal N}\Big)^2 K,\qquad \mathcal N=\frac{br\nu_E}{\mu_F(\nu_E+\mu_E)}.
$$

If $\Lambda\ge\mathcal S\,(e^{\mu_i T}-1)$, equivalently $T\le \frac{1}{\mu_i}\log\big(1+\Lambda/\mathcal S\big)$, then extinction is globally asymptotically stable for the periodically forced system, and $n\ge \tau(\underline M_i^{\mathrm{imp}})/T$ impulses suffice to drive the population from its wild equilibrium to extinction.

## Expansion

The release system is monotone with respect to the control, with sign pattern $(-,-,-,+)$ on $(E,M,M_i,F)$, so solutions with time-dependent $M_i$ are trapped between solutions of the constant-$M_i$ system at the extreme values of $M_i$. Above $M_i^{\mathrm{crit}}$ the constant system has extinction as its only equilibrium, which gives items 1 and 2; once the trajectory has entered the basin of extinction of the unreleased bistable system, releases can stop, which is why only finitely many releases are needed. Item 3 uses the explicit bound $M_i^{\mathrm{crit}}\le\frac{\mathcal N}{4\lambda\gamma_i}(1-1/\mathcal N)^2$ with $\lambda=\mu_M/((1-r)\nu_E K)$, so requiring $\underline M_i^{\mathrm{imp}}$ to exceed it gives the explicit amplitude–period trade-off $\Lambda\ge\mathcal S(e^{\mu_i T}-1)$; per release, the sterile-to-wild ratio needed is about $(e^{\mu_i T}-1)(\mathcal N-1)/(4\gamma_i)$.

## Depends on

- [Critical sterile-male density and bistability in the SIT/IIT mosquito model](critical-sterile-male-density-and-bistability-in-the-sit-iit-mosquito-model.md)

## Sources

- M. Strugarek, H. Bossin, Y. Dumont, *On the use of the sterile insect technique or the incompatible insect technique to reduce or eliminate mosquito populations*, arXiv:1805.10150 (2018). <https://doi.org/10.48550/arXiv.1805.10150> — Proposition 2.9 (constant releases), Lemmas 4–5 and Proposition 2.10 (periodic releases and number of releases), Propositions 2.11 and 2.13 (impulsive releases). Published version: Applied Mathematical Modelling 68 (2019), 443–470, <https://doi.org/10.1016/j.apm.2018.11.026>; locators above refer to the arXiv version.
