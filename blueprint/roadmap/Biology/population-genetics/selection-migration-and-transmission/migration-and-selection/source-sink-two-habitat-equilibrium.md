# Source–sink equilibrium in a two-habitat quantitative-trait model

**Model.** A population with a quantitative trait $z$ lives in two habitats with phenotype densities $n_i(t, z)$, growth rates $r_i(z) = r_{\max,i} - s_i(z - \theta_i)^2$ with $\theta_1 = -\theta$, $\theta_2 = \theta$, competition $\kappa_i > 0$, migration rates $m_i \ge 0$ out of habitat $i$, and asexual reproduction with mutation (rate $U$, kernel $\mu$ of mean $0$):

$$\partial_t n_i(z) = U\Bigl(\int n_i(z + y)\mu(y)\,dy - n_i(z)\Bigr) + n_i(z)\Bigl(r_i(z) - \kappa_i \int n_i(t, y)\,dy\Bigr) + m_j n_j(z) - m_i n_i(z),$$

for $(i, j) \in \{(1,2), (2,1)\}$. With $N_i = \int n_i$, mean $\mu_i$ and variance $\sigma_i^2$ of the trait in habitat $i$,

$$\frac{dN_i}{dt} = N_i(r_{\max,i} - \kappa_i N_i) - s_i N_i\bigl((\mu_i - \theta_i)^2 + \sigma_i^2\bigr) + m_j N_j - m_i N_i.$$

**Source–sink case.** Let $m_2 = 0$ (habitat 1 receives no migrants), $0 < m_1 < r_{\max,1}$ (the source persists and sends migrants to the sink), and consider the monomorphic equilibrium without mutation in which both habitats are concentrated at the habitat-1 optimum, $n_i = N_i \delta_{-\theta}$. Then

$$N_1^* = \frac{r_{\max,1} - m_1}{\kappa_1}, \qquad N_2^* = \frac{1}{2\kappa_2}\Bigl(r_{\max,2} - 4 s_2\theta^2 + \sqrt{(r_{\max,2} - 4 s_2\theta^2)^2 + 4\, m_1 (r_{\max,1} - m_1)\,\kappa_2/\kappa_1}\Bigr).$$

Because $m_1 > 0$, the square root exceeds $|r_{\max,2} - 4 s_2\theta^2|$, so the sink population persists ($N_2^* > 0$) even when $r_{\max,2} < 4 s_2 \theta^2$, i.e. when maladapted immigrants could not grow there on their own. Without immigration ($m_1 = m_2 = 0$) the same formula gives $N_2^* = \max(r_{\max,2} - 4 s_2\theta^2, 0)/\kappa_2$, which is $0$ when $r_{\max,2} \le 4 s_2 \theta^2$: persistence of a sink with negative intrinsic growth requires immigration. Mirrahimi and Gandon give the condition on the parameters under which this monomorphic state, rather than a dimorphic one with a locally adapted sink type, is the evolutionary equilibrium, and the small-mutation corrections to the phenotype distributions.

## Expansion

Integrating the PDE in $z$ kills the mutation term (the kernel preserves mass) and $\int n_i (z - \theta_i)^2 = N_i((\mu_i - \theta_i)^2 + \sigma_i^2)$ gives the $N_i$ equation. With $m_2 = 0$, habitat 1 is closed except for emigration, and at $\mu_1 = -\theta$, $\sigma_1 = 0$ its equation is $0 = N_1(r_{\max,1} - m_1 - \kappa_1 N_1)$. In habitat 2, $(\mu_2 - \theta_2)^2 = 4\theta^2$ and $0 = N_2(r_{\max,2} - 4s_2\theta^2 - \kappa_2 N_2) + m_1 N_1^*$, a quadratic whose positive root is $N_2^*$. With $a = r_{\max,2} - 4 s_2\theta^2$ and $b = m_1 N_1^* > 0$, the roots of $\kappa_2 N^2 - a N - b = 0$ are $(a \pm \sqrt{a^2 + 4\kappa_2 b})/(2\kappa_2)$, of which exactly one is positive since $b > 0$. The haploid [island model](migration-selection-balance-on-an-island.md) is the population-genetic analogue of a habitat that receives one-way migration.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof integrates the equation in $z$ and solves a quadratic, as the Expansion describes.

## Sources

- S. Mirrahimi and S. Gandon, "Evolution of specialization in heterogeneous environments: equilibrium between selection, mutation and migration", *Genetics* 214 (2020), <https://doi.org/10.1534/genetics.119.302868> (PMC7017023). Section 2, equations (1)–(5), and the source–sink scenario of Section 3.
