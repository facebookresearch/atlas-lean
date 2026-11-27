# Matroid prophet inequality

Let $\mathcal{M} = (E, \mathcal{I})$ be a matroid on a finite ground set $E$ and let $(X_e)_{e \in E}$ be independent nonnegative random weights with known distributions and finite means, so that the benchmark $\mathbb{E}[\max_{I \in \mathcal{I}} X(I)]$ is finite and a maximum-weight independent set exists. Elements arrive one by one in an adversarial order; on seeing $X_e$ the gambler must irrevocably decide whether to add $e$ to the selected set $S$, which must remain independent. The *matroid prophet ratio* of $\mathcal{M}$ is the supremum of the $c$ such that some online policy guarantees $\mathbb{E}[X(S)] \ge c\, \mathbb{E}[\max_{I \in \mathcal{I}} X(I)]$ for all weight distributions.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](../random-order-and-iid-prophet-inequalities/prophet-ratio-by-arrival-model.md)

## Sources

- Robert Kleinberg, S. Matthew Weinberg, "Matroid Prophet Inequalities", STOC (2012); Games and Economic Behavior 113 (2019), arXiv:1201.4764, Section 2.
