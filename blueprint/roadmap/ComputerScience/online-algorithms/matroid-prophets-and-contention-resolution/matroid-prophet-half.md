# Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality

For every matroid, every arrival order and all independent weight distributions, there is an online threshold policy with $\mathbb{E}[X(S)] \ge \frac12\,\mathbb{E}[\max_{I \in \mathcal{I}} X(I)]$. The constant $\frac12$ is optimal already for the rank-one matroid.

## Proof sketch

Set for each arriving element a *balanced threshold* equal to half the expected loss of value that accepting it would cause to the prophet's optimum restricted to the remaining elements, given the current selection. Kleinberg and Weinberg show that the accepted value pays for half of the prophet's optimum by splitting the optimum into the part blocked by accepted elements and the part still available, and using matroid exchange to bound each part. The single-item instance with values $1$ and $1/\varepsilon$ shows tightness.

## Depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Proof depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Sources

- Robert Kleinberg, S. Matthew Weinberg, "Matroid Prophet Inequalities", STOC (2012); Games and Economic Behavior 113 (2019), arXiv:1201.4764.
