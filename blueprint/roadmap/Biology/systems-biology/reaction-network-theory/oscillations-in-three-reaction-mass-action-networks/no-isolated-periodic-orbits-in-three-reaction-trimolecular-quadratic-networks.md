# No isolated periodic orbits in three-reaction trimolecular quadratic networks

**Setting.** A mass-action network is **quadratic** if every source complex has molecularity at most
two, and **trimolecular** if additionally every target complex has molecularity at most three. Three
reactions is the minimum number for oscillation, and a three-reaction system with a periodic orbit
must have rank two.

**Theorem 1.** Three-reaction, trimolecular, quadratic mass-action systems admit no isolated periodic
orbit, regardless of the number of species. Whenever such a system has a periodic orbit, all nearby
orbits are periodic as well.

**Theorem 4 (characterization).** If a three-reaction, quadratic, trimolecular mass-action system with
no trivial species has a periodic orbit, then up to a permutation of species its differential equation
belongs to one of three families: one related to the Lotka reactions, one related to the Ivanova
reactions, or the lifted Lotka–Volterra–Autocatalator. Including networks with trivial species, exactly
16 three-reaction, quadratic, trimolecular networks admit a periodic orbit with mass-action kinetics.

Supporting results:

- **Lemma 2.** A rank-two mass-action system whose source complexes lie on a line admits no periodic
  orbit.
- **Corollary 1.** If a rank-two, trimolecular, quadratic mass-action network with no trivial species
  admits an isolated periodic orbit, it contains a reaction $2X_j \to 3X_j$ for some species $X_j$.
- **Theorem 2.** Three-reaction, two-species, trimolecular, quadratic mass-action systems admit no
  isolated periodic orbit.
- **Lemmas 6–8.** With the reaction $2X \to 3X$ present and no trivial species: for three species only
  the lifted LVA family can have a periodic orbit; for four species every positive equilibrium is a
  saddle; for five or more species the network is dynamically trivial.

Hence a three-reaction quadratic system with an isolated periodic orbit needs a target complex of
molecularity at least four. **Theorem 3** classifies the planar three-reaction quadratic systems with
an Andronov–Hopf bifurcation: exactly two families admit a supercritical bifurcation (hence a stable
limit cycle), with source complexes $\{2X, X+Y, Y\}$ and $\{2X, X+Y, 0\}$; exactly four of the networks with an
Andronov–Hopf bifurcation are tetramolecular (all supercritical, in the first family), every other one
has a target complex of molecularity at least five, and every network of the second family has a target
complex of molecularity at least seven.

## Depends on

- [Vertical Andronov–Hopf bifurcation in the lifted Lotka–Volterra–Autocatalator](vertical-andronov-hopf-bifurcation-in-the-lifted-lotka-volterra-autocatalator.md)

## Proof depends on

- [Orientation formula for the Jacobian determinant of three-reaction networks](orientation-formula-for-the-jacobian-determinant-of-three-reaction-networks.md)

## Expansion

Without a reaction $2X_j\to3X_j$, a divergence computation with a Dulac function (Bendixson–Dulac
test) shows that in quadratic trimolecular rank-two systems an isolated periodic orbit is impossible
(Lemma 3), and the three-reaction systems where periodic orbits occur at all are the Lotka and Ivanova
reactions and two related two-parameter families, all with centres (Lemma 4). With $2X\to3X$ present,
the planar case reduces via the orientation formula and the trace of the Jacobian to the generalized
LVA, whose positive equilibrium is a repellor with no periodic orbit; in higher dimension the species
count is controlled by Lemmas 6–8, leaving only the lifted LVA, whose periodic orbits form a
two-parameter family at a vertical Hopf point. Known oscillators such as the Selkov model (cubic
sources) or a four-reaction extension of the LVA show that the bounds on the number of reactions and
on molecularities cannot be dropped.

## Sources

- M. Banaji, B. Boros, J. Hofbauer, "Oscillations in three-reaction quadratic mass-action systems", Studies in Applied Mathematics (2024), <https://doi.org/10.1111/sapm.12639> (PMC10953466). Theorem 1, Lemma 2, Lemma 3, Corollary 1, Lemma 4, Theorem 2, Theorem 3, Theorem 4, Lemmas 6–8, Figure 1, Introduction.
