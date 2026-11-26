# Serial and parallel reactions fix the sign of metabolic epistasis

**Topological relations.** Let $\mu$ be a metabolic module of first-order reversible reactions with
two input/output (I/O) metabolites and effective rate constant $y_\mu$. Two reactions of $\mu$ are

- **parallel** if there are at least two distinct simple paths within $\mu$ joining the I/O
  metabolites, each containing exactly one of the two reactions;
- **serial** if some simple path within $\mu$ joining the I/O metabolites contains both reactions;
- **strictly parallel** if parallel but not serial, and **strictly serial** if serial but not
  parallel (a pair that is both is serial–parallel).

**Theorem.** Let $\xi$ and $\eta$ be the rate constants of two different reactions in $\mu$, and let
mutation $A$ perturb only the first by $\delta_A \xi$ and mutation $B$ only the second by
$\delta_B \eta$. Write $\varepsilon y_\mu = (\delta_{AB} y_\mu - \delta_A y_\mu - \delta_B y_\mu) /
(2\,\delta_A y_\mu\, \delta_B y_\mu)$. In the limit $\delta_A \xi \to 0$, $\delta_B \eta \to 0$:

1. if the reactions are strictly parallel, then $\varepsilon y_\mu \le 0$;
2. if the reactions are strictly serial, then $\varepsilon y_\mu \ge 1$.

Serial–parallel pairs can show negative, weakly positive ($0 < \varepsilon < 1$) or strongly positive
($\varepsilon > 1$) epistasis depending on the rate constants.

## Depends on

- [Propagation of epistasis through metabolic modules](propagation-of-epistasis-through-metabolic-modules.md)

## Expansion

Writing $y_\mu = f_2(\xi, \eta)$, the small-effect limit gives

$$\varepsilon y_\mu = \frac{H_{\xi\eta}}{2\, C_\xi C_\eta} + o(1), \qquad
C_\xi = \frac{\partial f_2}{\partial \xi}\frac{\xi}{y_\mu}, \quad
C_\eta = \frac{\partial f_2}{\partial \eta}\frac{\eta}{y_\mu}, \quad
H_{\xi\eta} = \frac{\partial^2 f_2}{\partial \xi\, \partial \eta}\frac{\xi \eta}{y_\mu},$$

so the sign and size of epistasis are those of a normalized mixed second derivative. Coarse-graining
all other metabolites reduces every module, relative to a pair of focal reactions, to one of nine
topological classes, each with an explicit parametric form of $f_2$; checking the mixed derivative
class by class gives the theorem. Intuitively, parallel routes substitute for each other, so
improving one makes the other matter less (diminishing returns, $\varepsilon \le 0$), while serial
steps share one flux, so each mutation raises the control exerted by the other. In a small example
in which a third reaction of rate $z$ shunts flux, the affected pair is strictly parallel at $z = 0$
and effectively serial as $z \to \infty$, and $\varepsilon$ moves from negative through weak to strong
positive values. Combined with the propagation theorem, negative epistasis between parallel
reactions persists at every higher level of the metabolic hierarchy.

## Sources

- S. Kryazhimskiy, "Emergence and propagation of epistasis in metabolic networks", eLife 10 (2021)
  e60200, definitions of parallel and serial reactions, Theorem 2 and its proof in Materials and
  methods, <https://doi.org/10.7554/eLife.60200> (PMC7924954).
