# Mutation-weighted reproductive value

Consider a population of fixed size $N$ on sites $1, \dots, N$ updated by replacement events under neutral drift. Let $e^\circ_{ij}$ be the probability that the individual at $i$ replaces the one at $j$ in one step, and $d^\circ_i = \sum_j e^\circ_{ji}$ the probability that $i$ dies. Each offspring mutates with probability $u \in (0,1]$.

**Ancestral walk.** $A_{ij} = e^\circ_{ji}/d^\circ_i$ is the probability that the parent of $i$ sat at $j$, given that $i$ died. If at least one site can propagate its offspring to every site, $A$ has a unique stationary distribution $z$ ($z_i = \sum_j z_j A_{ji}$), and the classical reproductive value is $\pi_i = z_i/d^\circ_i$; it solves $\pi_i = (1 - d^\circ_i)\pi_i + \sum_j e^\circ_{ij}\pi_j$.

**First ancestral mutation.** Tracing the lineage of the individual at $j$ backwards, each step is mutation-free with probability $1 - u$. The probability that the first mutation on this lineage happens at site $i$ is

$$\sum_{t=0}^{\infty} u(1-u)^t (A^t)_{ji} = u\big[(I - (1-u)A)^{-1}\big]_{ji} .$$

Averaging over a uniformly chosen starting site gives the distribution

$$z^{\mathrm{mut}}_i = \frac1N\sum_{j=1}^N u\big[(I - (1-u)A)^{-1}\big]_{ji}, \qquad \sum_i z^{\mathrm{mut}}_i = 1,$$

and the **mutation-weighted reproductive value** is $\pi^{\mathrm{mut}}_i = z^{\mathrm{mut}}_i/d^\circ_i$. As $u \to 0$, $z^{\mathrm{mut}} \to z$ and $\pi^{\mathrm{mut}} \to \pi$; as $u \to 1$, $z^{\mathrm{mut}}$ becomes uniform and $\pi^{\mathrm{mut}}_i \to 1/(N d^\circ_i)$.

## Proof depends on

- [Neumann series for the Leontief inverse when row sums are below one](../../../../../Economics/general-equilibrium/leontief-input-output-model/has-sum-pow-of-row-sum-lt-one.md)

## Proof sketch

The geometric series sums because $A$ is stochastic and $(1-u) < 1$, so $(1-u)A$ has spectral radius below $1$. Row sums of $u(I - (1-u)A)^{-1}$ equal $u\sum_t(1-u)^t = 1$, so each row is a probability distribution over the site of the first mutation, and so is their average. At small $u$ the lineage wanders many steps before mutating and forgets its start, giving the stationary $z$; at $u = 1$ the mutation happens immediately at the starting site. The factor $1/d^\circ_i$ converts the ancestral-walk weight into time spent at $i$, just as for the classical reproductive value. The quantity $\pi^{\mathrm{mut}}$ weights selective events at site $i$ in the [structure coefficients for asymmetric games](structure-coefficients-for-asymmetric-games.md) (Eqs. (7)–(8) of the source).

## Sources

- A. McAvoy, J. Wakeley, "Evaluating the structure-coefficient theorem of evolutionary game theory", Proceedings of the National Academy of Sciences of the USA (2022), <https://doi.org/10.1073/pnas.2119656119> (PMC9282417).
