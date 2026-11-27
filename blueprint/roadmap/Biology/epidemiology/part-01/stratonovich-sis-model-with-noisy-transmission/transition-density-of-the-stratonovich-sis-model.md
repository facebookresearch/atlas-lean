# Transition density of the Stratonovich SIS model with noisy transmission

**Model.** In a population of constant size $N$ (recruitment balancing natural death rate $\mu$), with transmission rate $\beta$, recovery rate $\gamma$ and the transmission perturbed as $\beta\,dt \mapsto \beta\,dt + \sigma\,dW(t)$, the number infected solves the Stratonovich equation

$$dI = \Big(\frac{\beta}{N}(N-I)I - (\mu+\gamma)I\Big)dt + \frac{\sigma}{N}(N-I)I\circ dW(t), \qquad S = N - I,$$

which has a unique solution in $(0,N)$ for $I_0 \in (0,N)$. Let $R_0 = \beta/(\mu+\gamma)$ and

$$\bar A = \frac{2}{\sigma^2}\Big(\beta - (\mu+\gamma) - \frac{\sigma^2}{2}\Big), \qquad \bar C = \frac{2(\mu+\gamma)}{\sigma^2},$$

so that $\bar A + 1 > 0 \iff R_0 > 1$.

**Extinction.** If $R_0 < 1$, then $\limsup_{t\to\infty} t^{-1}\ln I(t) \le \beta - (\mu+\gamma) < 0$ almost surely: the infection dies out exponentially fast.

**Reduction.** With $x = \bar C\,I/(N-I)$, the Itô equation for $x$ is

$$dx = \frac{\sigma^2}{2}x(\bar A + 2 - x)\,dt + \sigma x\,dW(t).$$

**Theorem (stationary and transition densities).** Assume $x_0 > 0$ and $\bar A + 1 > 0$. Then $x$ has the unique stationary density

$$p^s_X(x) = \frac{x^{\bar A}e^{-x}}{\Gamma(\bar A+1)}, \qquad x > 0,$$

(a Gamma$(\bar A+1, 1)$ law), equivalently

$$p^s_I(I) = \frac{N\,\bar C^{\bar A+1}}{\Gamma(\bar A+1)}\,\frac{I^{\bar A}}{(N-I)^{\bar A+2}}\exp\!\Big(-\frac{\bar C I}{N-I}\Big), \qquad 0 < I < N,$$

with distribution function $\gamma(\bar A+1, \bar C I/(N-I))/\Gamma(\bar A+1)$. The transition density $p_X(x\mid t, x_0)$ is the eigenfunction expansion of the Fokker–Planck operator consisting of
- a discrete part with eigenvalues $r_n = \frac{\sigma^2}{2}n(\bar A+1-n)$ for the integers $0 \le n \le M$, where $\frac{\bar A+1}{2} - 1 \le M < \frac{\bar A+1}{2}$, with eigenfunctions built from $x^{-n}L_n^{(\alpha_n)}(x)$, $\alpha_n = \bar A + 1 - 2n$, $L_n^{(\alpha)}$ the generalized Laguerre polynomials; the $n = 0$ term is the stationary density;
- a continuous part with eigenvalues $r(\eta) = \frac{\sigma^2}{2}\big(\big(\frac{\bar A+1}{2}\big)^2 + \eta^2\big)$, $\eta \ge 0$, with eigenfunctions proportional to $x^{-(1+\bar A)/2}e^{x/2}W_{(1+\bar A)/2,\,i\eta}(x)$, where $W_{k,\theta}$ is the Whittaker function.
All modes other than $n = 0$ decay, so $p_I(I\mid t,I_0) \to p^s_I(I)$ as $t \to \infty$; the densities of $I$ and $S$ follow by the change of variables.

## Depends on

- [Threshold theorem for the SIS model](../../sis-epidemic-model/deriv-infected-pos-iff.md)

## Expansion

The Stratonovich chain rule gives $dx = \frac{\bar C}{(1-i)^2}di$ for the infected fraction $i = I/N$, hence $dx = \big((\beta-\mu-\gamma)x - \frac{\mu+\gamma}{\bar C}x^2\big)dt + \sigma x\circ dW$; converting to Itô adds $\frac{\sigma^2}{2}x\,dt$, which is the stated drift. The stationary Fokker–Planck solution is $p \propto (\sigma x)^{-2}\exp\!\big(\int \frac{(\bar A+2-y)}{y}dy\big) = x^{\bar A}e^{-x}$, integrable at $0$ exactly when $\bar A + 1 > 0$. Separating variables in $\partial_t p = -\partial_x\big(\frac{\sigma^2}{2}x(\bar A+2-x)p\big) + \frac12\partial_x^2(\sigma^2x^2p)$ leads to a Whittaker equation; its square-integrable solutions give the finitely many Laguerre modes, and the remaining spectrum above $\frac{\sigma^2}{2}\big(\frac{\bar A+1}{2}\big)^2$ is continuous. For extinction, Itô's formula gives $d\ln I \le (\beta-\mu-\gamma)\,dt + \frac{\sigma}{N}(N-I)\,dW$, and the strong law for martingales controls the noise term.

## Sources

- O. M. Otunuga, "Time-dependent probability distribution for number of infection in a stochastic SIS model: case study COVID-19", Chaos, Solitons & Fractals (2021) 110983, Eqs. (2.4)–(2.10), Theorem 1, Theorem 2, Theorem 3 (Eq. (3.30)), Remark 3 and Eq. (3.35), <https://doi.org/10.1016/j.chaos.2021.110983>, PMCID PMC8112579.
