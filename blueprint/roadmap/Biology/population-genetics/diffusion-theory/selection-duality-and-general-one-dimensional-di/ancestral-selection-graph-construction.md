# Construction of the ancestral selection graph

In the two-type Moran model with directional selection and mutation, the types of an $n$-sample and its genealogy are obtained in two stages (Birkner, Observation 3.4.5, after Krone and Neuhauser 1997). Backward in time, ancestral lines merge when they meet at a resampling event and split when hit by the tip of a selective arrow, and are traced until a single line, the ultimate ancestor, remains; forward in time, mutations are placed on the lines, which determines the types and resolves each potential branching (a selective arrow is used exactly when its source carries the favoured type). In the diffusion scaling, with $\sigma$ the scaled selection coefficient and $\theta_A$, $\theta_a$ the scaled mutation rates to the favoured type $A$ and to $a$, the number of potential ancestral lines converges to the Markov chain on $\{0, 1, 2, \dots\}$ that jumps from $i$ to $i + 1$ at rate $\sigma i/2$ (each line branches at rate $\sigma/2$), to $i - 1$ at rate $\binom i2 + i\theta_a/2$ (pairs merge at rate $1$, a line ends at rate $\theta_a/2$), and is killed at rate $i\theta_A/2$ (Observation 3.4.6). The target is the construction: the branching–coalescing graph, almost-sure finiteness of the time to the ultimate ancestor, the forward type assignment and resolution of branchings, and the pruned genealogy of the sample.


## Expansion

1. The graphical construction of the Moran model with selective arrows and mutation events.
2. The backward branching–coalescing process, its line count, non-explosion, and the almost-sure finite time to the ultimate ancestor (births are linear and coalescences quadratic in the number of lines).
3. The forward type assignment along the graph and the rule at branching events.
4. Pruning to the true genealogy and the law of the sample's types.
5. The diffusion limit of the line-counting process and its own generator, with branching at rate $\sigma i/2$, ending at rate $i\theta_a/2$ and killing at rate $i\theta_A/2$. For background only: without mutation and with $\sigma/2$ in place of $\sigma$ it reduces to the [line-counting generator](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-generator.md); its moment duality with the Wright–Fisher diffusion with selection is a separate statement.

## Sources

- Original result: S. M. Krone and C. Neuhauser, Ancestral processes with selection, Theor. Popul. Biol. 51 (1997), 210–237. <https://doi.org/10.1006/tpbi.1997.1299> The construction follows Birkner, Sec. 3.4.1.
- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, Sec. 3.4.1: Observations 3.4.5 and 3.4.6.
