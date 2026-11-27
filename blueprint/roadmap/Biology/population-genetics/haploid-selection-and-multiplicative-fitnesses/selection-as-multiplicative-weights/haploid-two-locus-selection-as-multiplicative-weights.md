# Haploid two-locus selection as multiplicative weights and loss of diversity

**Model.** A haploid population carries alleles $i \in S_1 = \{1, \dots, m\}$ at one locus and $j \in S_2 = \{1, \dots, n\}$ at another. Under weak selection with fitness matrix $B = \mathbf{1}_{m \times n} + \varepsilon C$ (fitness $B_{ij}$ for genotype $(i,j)$) and in the regime where the population stays in linkage equilibrium, the allele frequencies $\boldsymbol x \in \Delta_m$, $\boldsymbol y \in \Delta_n$ evolve by

$$x_i(t+1) = x_i(t)\,\frac{(B\boldsymbol y(t))_i}{\boldsymbol x(t)^{\mathsf T}B\boldsymbol y(t)}, \qquad y_j(t+1) = y_j(t)\,\frac{(B^{\mathsf T}\boldsymbol x(t))_j}{\boldsymbol x(t)^{\mathsf T}B\boldsymbol y(t)}.$$

This is the discrete replicator dynamics, equivalently the multiplicative weights update algorithm, for the *coordination game* $(B, B)$ in which the two loci are players, alleles are strategies and both receive the genotype fitness. A Nash equilibrium is *weakly stable* if fixing either player to any pure strategy in its support leaves the other indifferent among the strategies in its own support.

**Theorem.**
1. *(Convergence.)* Every orbit converges to a single fixed point $(\boldsymbol p, \boldsymbol q)$, and the update map is a diffeomorphism of $\Delta_m \times \Delta_n$ (smooth, bijective, with smooth inverse).
2. *(Unstable fixed points are avoided.)* The set of initial conditions converging to linearly unstable fixed points (Jacobian with an eigenvalue of modulus $> 1$) has Lebesgue measure zero; every linearly stable fixed point is a weakly stable Nash equilibrium.
3. *(Main result.)* For a coordination game with $B_{ij} \in [1 - s, 1 + s]$, $s < 1$, for all initial conditions outside a measure-zero set the dynamics converges to a weakly stable Nash equilibrium. If moreover the entries in each row and each column of $B$ are distinct, it converges to a pure Nash equilibrium: a single allele fixes at each locus.

## Expansion

Convergence follows from the fitness $\boldsymbol x^{\mathsf T}B\boldsymbol y$ being a potential that increases along the dynamics (Baum–Eagon), so no cycles occur. Because the map is a diffeomorphism, the center-stable manifold theorem shows that the basin of each linearly unstable fixed point is contained in a countable union of lower-dimensional manifolds, hence null. Linear stability forces the trace condition behind weak stability, and distinct payoffs leave no room for mixed weakly stable equilibria. Generically, then, selection in this model eliminates all polymorphism: what looks like a learning algorithm optimizing mean fitness also drives genetic diversity to zero, which is the inhibitor of diversity in the title.

## Sources

- Ruta Mehta, Ioannis Panageas and Georgios Piliouras, "Natural Selection as an Inhibitor of Genetic Diversity", in Proceedings of the 2015 Conference on Innovations in Theoretical Computer Science (ITCS 2015), ACM (2015), 73, <https://doi.org/10.1145/2688073.2688118>. Numbering follows the arXiv version, arXiv:1408.6270 (2014): Section 1 update rule, Theorem 4 (convergence and diffeomorphism), Lemma 6 (distinct entries), Lemmas 9–10 (stable fixed points are weakly stable equilibria), Theorem 12 (unstable fixed points are avoided) and Theorem 13 (main result), <https://doi.org/10.48550/arXiv.1408.6270>.
