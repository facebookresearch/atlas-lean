# Radiation model of commuting fluxes

Let locations $i$ have populations $m_i > 0$, let $T_i$ be the number of residents of $i$ who commute, and let $r_{ij}$ be the distance from $i$ to $j$. Let $s_{ij}$ be the total population living within distance $r_{ij}$ of $i$, excluding the populations of $i$ and $j$. The radiation model assigns to each ordered pair $i \ne j$ the commuting flux

$$T_{ij} = T_i\, \frac{m_i\, n_j}{(m_i + s_{ij})(m_i + n_j + s_{ij})}, \qquad n_j = m_j. \tag{1}$$

Properties:

- each term splits as $\dfrac{m_i n_j}{(m_i + s_{ij})(m_i + n_j + s_{ij})} = \dfrac{m_i}{m_i + s_{ij}} - \dfrac{m_i}{m_i + n_j + s_{ij}}$;
- if the destinations $j_1, j_2, \dots, j_L$ of $i$ are ordered by increasing distance with no ties, then $s_{i j_{\ell+1}} = s_{i j_\ell} + n_{j_\ell}$, the sum telescopes, and the total predicted outflow is

$$\sum_{j \ne i} T_{ij} = T_i\left(1 - \frac{m_i}{m_i + \sum_{j \ne i} n_j}\right) = T_i\left(1 - \frac{m_i}{M}\right),$$

with $M$ the total population; so a finite system assigns slightly fewer than $T_i$ commuters, and the shortfall is the fraction $m_i / M$;
- the flux depends on distance only through the intervening population $s_{ij}$, so it does not change when the region is stretched or compressed in a way that preserves the distance order of destinations.

## Expansion

The model arises from a decision process in which each commuter takes the closest job offer whose benefit exceeds the best offer at home, with offers proportional to population; the probability that a commuter from $i$ lands in $j$ is the expression multiplying $T_i$. The first term of the split is the probability that no acceptable offer occurs within $s_{ij}$, and the second removes the probability that none occurs within $s_{ij} + n_j$. In metapopulation models of influenza-like illness in three European countries, radiation-model networks reproduced census commuting well and gave slower epidemic arrival than census networks. They matched the order of invasion better than mobile-phone proxies for centrally seeded epidemics, while phone proxies did better for peripheral seeds.

## Sources

- M. Tizzoni, P. Bajardi, A. Decuyper, et al., "On the use of human mobility proxies for modeling epidemics", PLoS Computational Biology 10(7) (2014) e1003716, Materials and Methods, radiation model Eq. (1), and Results, "Epidemic simulations", <https://doi.org/10.1371/journal.pcbi.1003716> (PMC4091706).
- F. Simini, M. C. González, A. Maritan, A.-L. Barabási, "A universal model for mobility and migration patterns", Nature 484 (2012) 96–100, original derivation of the model, <https://doi.org/10.1038/nature10856>.
