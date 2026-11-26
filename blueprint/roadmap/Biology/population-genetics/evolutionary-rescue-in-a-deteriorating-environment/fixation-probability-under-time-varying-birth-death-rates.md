# Fixation probability of a mutant under time-varying birth and death rates

**Model.** Asexual organisms of wild type $W$ and mutant type $M$ share a carrying capacity $K$. An organism of type $i$ divides at rate $f_i(t)(1 - N/K)$, where $N$ is the total population size and $f_i(t)$ the time-dependent fitness, and dies at constant rate $g_i$. In a deteriorating environment the wild-type fitness decays, for instance as the Hill function

$$f_W(t) = \frac{1}{1 + (t/\theta)^n},$$

and the wild-type population is described deterministically by

$$\frac{dN_W}{dt} = \Bigl[f_W(t)\Bigl(1 - \frac{N_W}{K}\Bigr) - g_W\Bigr] N_W .$$

Mutants are few when they arise, so while $N_M \ll N_W$ a mutant lineage is a linear birth–death process with birth rate $f_M(t)(1 - N_W(t)/K)$ and death rate $g_M$.

**Proposition.** The probability that a single mutant appearing at time $t_0$ founds a lineage that does not go extinct is

$$p_{\mathrm{fix}}(t_0) = \frac{1}{1 + g_M \int_{t_0}^{\infty} e^{\rho(t)}\, dt}, \qquad \rho(t) = \int_{t_0}^{t} \Bigl[g_M - f_M(u)\Bigl(1 - \frac{N_W(u)}{K}\Bigr)\Bigr] du .$$

If the wild type is still present but about to vanish, $p_{\mathrm{fix}} \to 1 - g_M/f_M$ for a mutant of constant fitness $f_M$.

## Expansion

Let $\varphi(z,t) = \sum_i z^i P(i, t \mid 1, t_0)$ be the generating function of the mutant count. It solves the first-order linear PDE of a birth–death process with rates $\lambda(t)$ and $\mu$, whose solution by characteristics gives the classical extinction probability $\lim_{t\to\infty}\varphi(0,t)$ of a time-inhomogeneous linear birth–death process; $p_{\mathrm{fix}} = 1 - \lim_{t \to \infty} \varphi(0,t)$. Mutants arising later have larger $p_{\mathrm{fix}}$, both because their selective advantage grows and because competition with the decaying wild type weakens. With constant rates and no competition the formula reduces to $1 - g_M/f_M$, the survival probability of a supercritical linear birth–death process.

## Sources

- L. Marrec and A.-F. Bitbol, "Adapt or Perish: Evolutionary Rescue in a Gradually Deteriorating Environment", *Genetics* (2020), <https://doi.org/10.1534/genetics.120.303624> (PMC7536851; Equations (1), (3), (4) and (5)).
