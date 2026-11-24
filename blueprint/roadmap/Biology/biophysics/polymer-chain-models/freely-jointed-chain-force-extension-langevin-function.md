# Force–extension of the freely jointed chain

A three-dimensional freely jointed chain consists of $n \ge 1$ independent segments of length $l > 0$ with directions on the unit sphere and no interaction energy. Under a constant force $f \ge 0$ on its end along a fixed axis at temperature $T > 0$, each segment direction has density proportional to $e^{\varphi\cos\theta}$ with respect to surface measure, $\varphi = f l/(k_B T)$, with one-segment partition function $z(\varphi) = \int_{S^2} e^{\varphi\cos\theta}\, d\Omega = 4\pi\sinh\varphi/\varphi$ for $\varphi > 0$ and $z(0) = 4\pi$. The mean extension along the force is

$$E[x] = n l\, \mathcal{L}(\varphi), \qquad \mathcal{L}(\varphi) = \coth\varphi - \frac1\varphi \ (\varphi > 0), \quad \mathcal{L}(0) = 0,$$

the Langevin function extended continuously at $0$. For $\varphi \to 0$, $E[x] = n l^2 f/(3 k_B T) + O(\varphi^3)$, a linear entropic spring with constant $3 k_B T/(n l^2)$; for $\varphi \to \infty$, $E[x] = n l\,(1 - 1/\varphi) + O(e^{-2\varphi})$ (Tokmakoff, Eqs. (9.3.5)–(9.3.7)).

## Expansion

1. The model: $n$ independent directions on the unit sphere with the Gibbs density $e^{\beta f l\cos\theta}$ with respect to surface measure (a continuous canonical ensemble; the finite counting-measure ensemble is an analogy, not this model).
2. The one-segment partition function, with its value at $\varphi = 0$, and the product over segments.
3. The mean extension as $k_B T\, \partial_f \ln Z$, giving the Langevin function, and its continuous extension at $0$.
4. The small-force and large-force expansions.

## Sources

- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Sec. 9.3 Polymer Elasticity and Force–Extension Behavior, Force/Extension Behavior for a Freely Jointed Chain, Eqs. (9.3.5)–(9.3.7). <https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_(Tokmakoff)/02:_Macromolecules/09:_Macromolecular_Mechanics/9.03:_Polymer_Elasticity_and_ForceExtension_Behavior> (The page writes $2\pi\sinh\varphi/\varphi$ for the partition function; integrating over the full solid angle gives $4\pi\sinh\varphi/\varphi$, and the constant factor does not affect the extension.)
- Original model: W. Kuhn and F. Grün, Beziehungen zwischen elastischen Konstanten und Dehnungsdoppelbrechung hochelastischer Stoffe, Kolloid-Z. 101 (1942), 248–271. The force–extension formula follows Tokmakoff, Sec. 9.3.
