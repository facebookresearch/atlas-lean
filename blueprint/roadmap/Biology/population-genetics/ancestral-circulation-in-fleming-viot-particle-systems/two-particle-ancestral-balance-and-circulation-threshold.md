# Two-particle ancestral balance and the circulation threshold in Fleming–Viot systems

**Model.** $N \ge 2$ particles move independently as an irreducible continuous-time Markov chain on a finite set $I$ ($|I| \ge 2$) with rates $q(i,j)$, reversible with respect to positive weights $\nu$: $\nu_i q(i,j) = \nu_j q(j,i)$. A particle at site $i$ is killed at rate $k_i > 0$ and instantly jumps onto a uniformly chosen other particle, adopting its position and its ancestral label (Fleming–Viot system); eventually one label fixes. Let $\pi_N$ be the stationary law of the site counts $c \in \mathbb N_0^I$, $|c| = N$, and $h_N(i,d)$ the probability that the label of a given particle at $i$ fixes when the others have counts $d$. Define the label-weighted transport and ancestral current

$$F^{(N)}_{ij} = \sum_{c:\,c_i > 0}\pi_N(c)\,c_i\,h_N(j, c - e_i), \qquad J^{(N)}_{ij} = q(i,j)F^{(N)}_{ij} - q(j,i)F^{(N)}_{ji}.$$

**Theorem.**
1. For every finite reversible motion and every positive killing vector, the two-particle system is balanced:

$$\frac{F^{(2)}_{ij}}{\nu_i} = \frac{F^{(2)}_{ji}}{\nu_j} \quad (i,j \in I),$$

so all two-particle ancestral currents vanish. Indeed $F^{(2)}_{ij} = \frac{2\nu_i}{Z}\int_0^\infty p_t(i)p_t(j)\,dt$ for the sub-Markov kernel $p_t$ of the killed motion and a normalizing constant $Z$.
2. On the complete graph with three states ($q(i,j) = 1$, $\nu_i = 1$) and for each $N \ge 3$, the set of killing vectors $k \in (0,\infty)^3$ with $\Delta_N(k) = F^{(N)}_{02} - F^{(N)}_{20} \ne 0$ is open, dense and of full Lebesgue measure (its complement lies in a proper algebraic set), and the killing vectors giving nonzero circulation simultaneously for all $N \ge 3$ form a dense $G_\delta$ set of full measure.
3. For every $N$ the current is divergence-free, $\sum_{j \ne i}J^{(N)}_{ij} = 0$, hence vanishes on bridges; three sites and three particles are the minimal setting for circulation. With constant killing every label fixes with probability $1/N$ and all currents vanish.

## Expansion

With two particles the first death decides the ancestor, and the pair's stationary measure is given by a Green-kernel formula that is symmetric under exchanging the two sites, inherited from reversibility of the motion. From three particles on, ancestry is selected through successive reproduction events whose success depends on where the killing is heavy, and this breaks detailed balance of the label flow even though the motion is reversible. A perturbation of constant killing shows the first nonzero term of the current is cubic, and real-analyticity in $k$ upgrades one nonzero point to a generic set. Biologically, for rare transplants between sites, migration followed by fixation is more likely in one direction around a cycle than in the reverse.

## Sources

- Y. Lin, T. Lu, "Ancestral circulation beyond two Fleming-Viot particles", arXiv:2610.12589 (2026), main theorem of the Introduction, Proposition A.1 and Theorem A.2, <https://doi.org/10.48550/arXiv.2610.12589>.
