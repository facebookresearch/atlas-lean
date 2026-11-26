# Stochastic persistence despite deterministic impermanence

Consider two competing prey $X_1,X_2$ sharing a predator $X_3$ that uses a **switching functional response**: it hunts each prey in proportion to that prey's relative abundance. The deterministic model is

$$
\begin{aligned}
\dot X_1&=X_1\Bigl(r-X_1-\beta X_2-\tfrac{X_1}{X_1+X_2}X_3\Bigr),\\
\dot X_2&=X_2\Bigl(r-X_2-\beta X_1-\tfrac{X_2}{X_1+X_2}X_3\Bigr),\\
\dot X_3&=X_3\Bigl(\tfrac{X_1^2+X_2^2}{X_1+X_2}-d-cX_3\Bigr),
\end{aligned}
$$

with prey growth rate $r>0$, interspecific competition coefficient $\beta>0$, predator death rate $d$ and predator self-limitation $c>0$. The ODE is **permanent** if there is $m>0$ with $1/m\le\liminf_t\min_iX_i(t)\le\limsup_t\max_iX_i(t)\le m$ for every positive initial condition. The stochastic version adds independent environmental noise $\varepsilon X_i\,dB_i(t)$ to each equation.

**Proposition (deterministic).** Let $\beta>1$. If

$$
\frac{r}{1+\beta}>d\qquad\text{and}\qquad \frac{r}{\beta}\bigl(1+c(1-\beta)\bigr)>d,
$$

the ODE is permanent. If either inequality is reversed, it is not permanent.

**Proposition (stochastic).** Let $\beta>0$. If $\frac{r}{\beta}\bigl(1+c(1-\beta)\bigr)>d$ and $\varepsilon>0$ is sufficiently small, the stochastic system is strongly stochastically persistent: it has a unique invariant probability measure on $(0,\infty)^3$ that attracts all positive initial conditions.

**Consequence.** If $\beta>1$, $\frac{r}{\beta}>d>\frac{r}{1+\beta}$ and $c,\varepsilon>0$ are small enough, the deterministic three-species system is impermanent, yet its stochastic counterpart is strongly stochastically persistent.

## Depends on

- [Persistence–exclusion dichotomy for three-species stochastic Kolmogorov systems](persistence-exclusion-dichotomy-for-three-species-stochastic-kolmogorov-systems.md)

## Expansion

The deterministic prey subsystem has an internal equilibrium for species $1$ and $2$ at which the predator's invasion rate is $r/(1+\beta)-d$. When this is negative, that boundary equilibrium cannot be invaded and permanence fails. The stochastic model has no ergodic invariant measure supporting both prey, so this negative invasion rate never enters the stochastic analysis. For small noise, the remaining boundary ergodic measures (single-prey and prey–predator communities) are invadable under the stated inequality, and the invasion-rate persistence criterion gives strong stochastic persistence. So stochastic persistence is not a weaker form of deterministic permanence: noise can remove the boundary attractor that blocks coexistence.

## Sources

- A. Hening, D. H. Nguyen, S. J. Schreiber, "A classification of the dynamics of three-dimensional stochastic ecological systems", arXiv preprint (2020), Section 8 ("Stochastic Persistence Despite Deterministic Impermanence": Propositions 8.4–8.5 and the remark following them), <https://doi.org/10.48550/arXiv.2004.00535>.
