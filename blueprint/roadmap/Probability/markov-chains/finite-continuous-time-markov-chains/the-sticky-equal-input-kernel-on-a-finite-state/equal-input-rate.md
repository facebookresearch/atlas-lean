# Equal-input generator (F81 model)

For $\pi : S \to \mathbb{R}$ and a rate $\kappa \in \mathbb{R}$, the equal-input generator is the
$S \times S$ matrix

$$\kappa\, (\mathbf 1 \pi^\top - I), \qquad \text{with entries } \kappa\bigl(\pi(j) - [i = j]\bigr),$$

where $\mathbf 1 \pi^\top$ is the [equal-input matrix](equal-input.md). For $\kappa \ge 0$ and a
probability vector $\pi$, it generates the chain that jumps at rate $\kappa$ to a state drawn from
$\pi$: Felsenstein's F81 model, on an arbitrary finite state space.

## Sources

- J. Felsenstein, *Evolutionary trees from DNA sequences: a maximum likelihood approach*, Journal of
  Molecular Evolution 17 (1981), 368–376.
