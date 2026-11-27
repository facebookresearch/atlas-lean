# Equilibria and error thresholds of a three-population quasispecies model of tumorigenesis

**Model.** Let $x_0$ be the fraction of cells with anomalous growth and stable genomes, $x_1$ the fraction of genetically unstable cells and $x_2$ the fraction of malignant mutant cells (one mutant class), with fitnesses $f_0, f_1, f_2 > 0$ and copying fidelities $Q, Q'\in(0,1)$, i.e. mutation probabilities $\mu_0 = 1 - Q$ ($x_0\to x_1$) and $\mu_1 = 1 - Q'$ ($x_1\to x_2$):

$$\dot x_0 = f_0Qx_0 - \Phi x_0, \qquad \dot x_1 = f_0(1-Q)x_0 + f_1Q'x_1 - \Phi x_1, \qquad \dot x_2 = f_1(1-Q')x_1 + f_2x_2 - \Phi x_2,$$

with mean fitness $\Phi = f_0x_0 + f_1x_1 + f_2x_2$ (constant-population constraint). The simplex $x_0 + x_1 + x_2 = 1$ is invariant, since $\frac{d}{dt}(x_0+x_1+x_2) = \Phi\,(1 - (x_0+x_1+x_2))$.

**Theorem.** On the simplex the equilibria are:

1. **Malignant dominance** $(0,0,1)$, always present, with Jacobian eigenvalues $f_0Q - f_2$, $f_1Q' - f_2$, $-f_2$; it is a local attractor iff

$$f_0Q < f_2 \quad\text{and}\quad f_1Q' < f_2,$$

i.e. iff both mutation rates exceed the error thresholds $\mu_0 > 1 - f_2/f_0$ and $\mu_1 > 1 - f_2/f_1$.
2. **Unstable–malignant coexistence** $\Big(0, \dfrac{f_1Q' - f_2}{f_1 - f_2}, \dfrac{f_1(1 - Q')}{f_1 - f_2}\Big)$, admissible iff $f_1 > f_2$ and $f_1Q' > f_2$, with eigenvalues

$$f_0Q - f_1Q', \qquad f_2 - f_1Q', \qquad -f_1Q',$$

the last transverse to the simplex.

3. **Full coexistence**, where $\Phi = f_0Q$, given by

$$x_0^\ast = \frac{(f_0Q - f_1Q')(f_0Q - f_2)}{\varphi}, \quad x_1^\ast = \frac{f_0(1-Q)(f_0Q - f_2)}{\varphi}, \quad x_2^\ast = \frac{f_1(1-Q')f_0(1-Q)}{\varphi},$$

with $\varphi = (f_0Q - f_1Q')(f_0Q - f_2) + f_0(1-Q)(f_0Q - f_2) + f_1(1-Q')f_0(1-Q)$, admissible when these are positive.

If $f_1 = f_2$ (neutral mutants) the second equilibrium disappears. Transitions between these regimes as $f_0Q$ and $f_1Q'$ vary are transcritical exchanges of stability; with $Q' = 1$ the model reduces to the two-variable quasispecies model.

## Depends on

- [Eigen's quasispecies error threshold](../../population-dynamics/eigen-s-quasispecies-error-threshold/README.md)

## Expansion

On $\{x_0 = x_1 = 0\}$ the only point of the simplex is $(0,0,1)$; at it, $\Phi = f_2$, and the Jacobian is triangular, so its eigenvalues are the invasion rates $f_0Q - f_2$ and $f_1Q' - f_2$ of the two precursor populations, plus $-f_2$ transverse to the simplex. The malignant population therefore takes over exactly when neither precursor can sustain itself against the loss of offspring to mutation, which is the quasispecies error-threshold mechanism applied twice. With $x_0 = 0$ the remaining two equations are linear in $x_1$ after using $\Phi = f_1x_1 + f_2x_2$ and $x_1 + x_2 = 1$, giving the second equilibrium; with all populations present the $x_0$-equation forces $\Phi = f_0Q$ and the rest is a linear system. Along parameter paths crossing $f_1Q' = f_2$ or $f_0Q = f_1Q'$ the corresponding eigenvalue changes sign while two equilibria meet, so stability is exchanged.

## Sources

- Vanessa Castillo, J. Tomás Lázaro, Josep Sardanyés, "Dynamics and bifurcations in a simple quasispecies model of tumorigenesis", arXiv (2014). Section 2 (model, mean fitness), Section 3 (equilibrium points, Remark 3.1, first-integral lemma, stability analysis and bifurcations). <https://doi.org/10.48550/arXiv.1411.6531>. Published version: Computational and Applied Mathematics 36(1) (2017), 415–431, <https://doi.org/10.1007/s40314-015-0234-3>; locators above refer to the arXiv version.
