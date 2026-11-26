# Construction of the ancestral selection graph

In the two-type Moran model with directional selection and mutation, the types of an $n$-sample and its genealogy are obtained in two stages (Birkner, Observation 3.4.5(1), after Krone and Neuhauser 1997). Backward in time, ancestral lines merge when they meet at a resampling event and split when hit by the tip of a selective arrow, and are traced until a single line, the ultimate ancestor, remains; mutation events are not used to remove lines. Forward in time, mutations are placed on the lines, which determines the types and resolves each potential branching (a selective arrow is used exactly when its source carries the favoured type). In the diffusion scaling, with $\sigma$ the scaled selection coefficient, the line count of this full graph jumps from $i$ to $i + 1$ at rate $\sigma i/2$ and from $i$ to $i - 1$ at rate $\binom i2$; since births are linear and coalescences quadratic in the number of lines, it reaches one line in almost surely finite time.

A different backward process answers a narrower question (Birkner, Observation 3.4.5(2) and Observation 3.4.6): the event that *all* sampled individuals carry the unfavoured type $a$. Here a line hit by a mutation to $a$ is removed, since its type is then known to be $a$, and a mutation to the favoured type $A$ on any line sends the process to a cemetery state $\partial$, since the event then fails. The sample is all $a$ exactly when this process is not killed and every line it holds at the starting time carries type $a$. With $\theta_A$, $\theta_a$ the scaled mutation rates to $A$ and to $a$, its line count converges to the Markov chain on $\{0, 1, 2, \dots\} \cup \{\partial\}$ that jumps from $i$ to $i + 1$ at rate $\sigma i/2$, to $i - 1$ at rate $\binom i2 + i\theta_a/2$, and to $\partial$ at rate $i\theta_A/2$. This killed process can enter $\partial$ before reaching one line, so the full graph's almost-sure hitting of a single line is not a claim about it.

The target is the full construction: the branching–coalescing graph, almost-sure finiteness of the time to the ultimate ancestor, the forward type assignment and resolution of branchings, and the pruned genealogy of the sample; and, as a separate statement, the killed process with its representation of the event that the whole sample has type $a$.


## Expansion

1. The graphical construction of the Moran model with selective arrows and mutation events.
2. The backward branching–coalescing process of the full graph, its line count, non-explosion, and the almost-sure finite time to the ultimate ancestor (births are linear and coalescences quadratic in the number of lines).
3. The forward type assignment along the graph and the rule at branching events.
4. Pruning to the true genealogy and the law of the sample's types.
5. The killed backward process for the event that all sampled types are $a$ (line removal at mutations to $a$, cemetery at mutations to $A$), its representation of that event, and the diffusion limit of its line count with branching at rate $\sigma i/2$, coalescence at rate $\binom i2$, removal at rate $i\theta_a/2$ and killing at rate $i\theta_A/2$; no almost-sure hitting of one line is claimed for it. For background only: without mutation and with $\sigma/2$ in place of $\sigma$ it reduces to the [line-counting generator](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-generator.md); its moment duality with the Wright–Fisher diffusion with selection is a separate statement.

## Sources

- Original result: S. M. Krone and C. Neuhauser, Ancestral processes with selection, Theor. Popul. Biol. 51 (1997), 210–237. <https://doi.org/10.1006/tpbi.1997.1299> The construction follows Birkner, Sec. 3.4.1.
- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, Sec. 3.4.1: Observations 3.4.5 and 3.4.6.
