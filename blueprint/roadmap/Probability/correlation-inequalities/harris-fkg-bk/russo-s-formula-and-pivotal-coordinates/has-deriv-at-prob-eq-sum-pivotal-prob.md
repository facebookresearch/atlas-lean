# Russo's formula

Let $E$ be a finite set and $A \subseteq \{0,1\}^E$ an increasing event. For every $p \in \mathbb{R}$, the [event weight](prob.md) $p \mapsto P_p(A)$ is differentiable at $p$ with

$$\frac{d}{dp} P_p(A) = \sum_{e \in E} \mathrm{Piv}_p(A, e),$$

where $\mathrm{Piv}_p(A, e)$ is the [weight of the event that $e$ is pivotal](pivotal-prob.md) for $A$. For $p \in [0,1]$ this says that the derivative of $\mathbb{P}_p(A)$ is the expected number of pivotal coordinates.

## Sources

- L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981), 229–237.
- G. A. Margulis, *Probabilistic characteristics of graphs with large connectivity*, Problemy Peredači Informacii 10 (1974), 101–108.
