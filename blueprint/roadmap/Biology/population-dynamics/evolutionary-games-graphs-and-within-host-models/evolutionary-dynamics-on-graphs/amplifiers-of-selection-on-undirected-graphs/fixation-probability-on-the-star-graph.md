# Fixation probability on the Star graph

**Generalized Moran process on a graph.** Let $G_N = (V_N, E_N)$ be a connected undirected graph on $N$ vertices, each holding one individual. Mutants have fitness $r > 0$ and residents fitness $1$. In each step one individual is chosen to reproduce with probability proportional to fitness, and its offspring replaces a uniformly random neighbour of the reproducing vertex. Let $\rho(r, G_N)$ be the probability that a single mutant placed on a uniformly random vertex takes over the graph. For the complete graph (Clique) $K_N$, $\rho(r, K_N) = \dfrac{1 - r^{-1}}{1 - r^{-N}}$.

**Star.** The Star $S_N$ has one centre joined to $N - 1$ leaves and no other edges. For $r \ne 1$, put

$$h_c = \frac{r(N-1) + 1}{r(N-1) + r^2}, \qquad h_l = \frac{N - 1 + r}{r^2(N-1) + r} .$$

Then

$$\rho(r, S_N) = \frac{N-1}{N}\cdot\frac{h_l - 1}{h_c\,h_l^{\,N-1} - 1} + \frac1N\cdot\frac{h_c - 1}{h_c\,h_l^{\,N-1} - 1},$$

and for large $N$

$$\rho(r, S_N) \simeq \frac{1 - r^{-2}}{1 - r^{-2N}},$$

the Clique formula with $r$ replaced by $r^2$. For $r > 1$ the Star therefore amplifies selection; in the limit $N \to \infty$ its fixation probability tends to $1 - r^{-2}$ instead of $1 - r^{-1}$.

## Depends on

- [Fixation probability of the Moran process](../../../../population-genetics/moran-model/moran-fixation.md)

## Proof sketch

The state of the Star is the pair (type of the centre, number of mutant leaves), so the absorption equations reduce to a chain on about $2N$ states that can be solved in closed form; the formula above is the solution derived by Broom and Rychtář and quoted in the source, the two terms corresponding to an initial mutant on a leaf (probability $(N-1)/N$) or on the centre. For large $N$, a mutant leaf must first take the centre and then the centre must copy itself onto a resident leaf; both steps carry a fitness bias $r$, so the effective forward bias per gained leaf is $r^2$. The exact formula agrees with direct numerical solution of the absorption equations for small Stars (for example $\rho(2, S_3) = 7/12$ and $\rho(1.5, S_4) \approx 0.4462$), and at $N = 2$ it reduces to the Clique value $r/(1+r)$.

## Sources

- A. Pavlogiannis, J. Tkadlec, K. Chatterjee, M. A. Nowak, "Amplification on undirected population structures: Comets beat stars", Scientific Reports (2017), <https://doi.org/10.1038/s41598-017-00107-w> (PMC5427850).
- M. Broom, J. Rychtář, "An analysis of the fixation probability of a mutant on special classes of non-directed graphs", Proceedings of the Royal Society A 464 (2008) 2609–2627.
