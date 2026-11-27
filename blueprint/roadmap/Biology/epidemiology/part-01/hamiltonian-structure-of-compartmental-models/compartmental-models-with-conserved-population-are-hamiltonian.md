# Compartmental models with conserved population are Hamiltonian

Let $x^1, \dots, x^M$ be the sizes (or fractions) of the $M$ compartments of an epidemiological model, governed by

$$\dot x^\mu = f^\mu(x^1, \dots, x^{M-1}), \qquad \mu = 1, \dots, M,$$

with $f^1, \dots, f^M$ smooth and the total population conserved, $\dot x^1 + \dots + \dot x^M = 0$, so that $f^M = -(f^1 + \dots + f^{M-1})$.

**Theorem (Proposition 2 and Corollary 1 of the source).** The system is Hamiltonian with Hamiltonian the total population

$$H = \sum_{\mu=1}^{M} x^\mu$$

and the Poisson structure defined by the fundamental brackets

$$\{x^\mu, x^\nu\} = 0 \quad (\mu, \nu \le M-1), \qquad \{x^\mu, x^M\} = f^\mu(x^1, \dots, x^{M-1}) \quad (\mu \le M - 1).$$

That is, $\dot x^\mu = \{x^\mu, H\}$ for every $\mu$. Every compartmental model with constant population is therefore a Hamiltonian system, and choosing a different compartment as $x^M$ gives further Poisson structures with the same Hamiltonian.

For the generalized SIR model $\dot S = -\beta S I + \varphi_1(S, I)$, $\dot I = \beta S I - \alpha I + \varphi_2(S, I)$, $\dot R = \alpha I - \varphi_1 - \varphi_2$, which contains SIRS, vaccination and vital-dynamics variants, this gives $H = S + I + R$ with $\{S, I\} = 0$, $\{S, R\} = -\beta S I + \varphi_1$, $\{I, R\} = -\alpha I + \beta S I + \varphi_2$ (Proposition 1 of the source).

## Expansion

Hamilton's equations read $\dot x^\mu = \{x^\mu, H\} = \sum_\nu \{x^\mu, x^\nu\} = \{x^\mu, x^M\} = f^\mu$ for $\mu \le M-1$, and $\dot x^M = \sum_{\nu < M} \{x^M, x^\nu\} = -\sum_{\nu < M} f^\nu$, recovering the system. Every bracket is a function of $x^1, \dots, x^{M-1}$ only, and these coordinates Poisson-commute, so $\{g(x^1, \dots, x^{M-1}), x^\nu\} = 0$ for $\nu < M$; in each Jacobi expression every double bracket then vanishes. The Hamiltonian is conserved, and the dynamics lies on the level set $H = 1$ when compartments are fractions, which is how dependence on $x^M$ (for example on $R$) is absorbed by substituting $x^M = 1 - \sum_{\mu < M} x^\mu$. Models with exponentially growing total population and linear transfer terms reduce to this case after rescaling by the total population. The [conservation of the population in the Kermack-McKendrick model](../../kermack-mckendrick-sir-model/total-eq.md) is the special case $M = 3$, $\varphi_1 = \varphi_2 = 0$.

## Depends on

- [Conservation of the population](../../kermack-mckendrick-sir-model/total-eq.md)

## Sources

- A. Ballesteros, A. Blasco and I. Gutierrez-Sagredo, *Hamiltonian structure of compartmental epidemiological models*, Physica D 413 (2020), 132656. DOI: <https://doi.org/10.1016/j.physd.2020.132656>. PMCID: PMC7375975.
