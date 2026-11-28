# Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality

For every matroid on a finite ground set and all independent nonnegative weight distributions with finite means, there is a single online threshold policy, fixed before the arrival order is known, that guarantees $\mathbb{E}[X(S)] \ge \frac12\,\mathbb{E}[\max_{I \in \mathcal{I}} X(I)]$ against every arrival order, including orders chosen element by element by an adversary who has seen the weights revealed so far. The constant $\frac12$ is optimal already for the rank-one matroid.

## Proof sketch

Let $X'$ be an independent copy of the weights and $B$ a maximum-$X'$-weight basis. For an independent set $A$, split $B$ into $C(A)$ and $R(A)$ with $A \cup R(A)$ a basis, choosing the split that maximizes $X'(R(A))$. When $e$ arrives and $A \cup \{e\}$ is independent for the current selection $A$, the *balanced threshold* is $\frac12\mathbb{E}\big[X'(R(A)) - X'(R(A \cup \{e\}))\big]$, half the expected value that accepting $e$ removes from what the independent prophet could still add; otherwise the threshold is $\infty$. Kleinberg and Weinberg show that the accepted value pays for half of the prophet's optimum by splitting the optimum into the part blocked by accepted elements and the part still available, and using matroid exchange to bound each part. Tightness: a rank-one instance with first weight $1$ and second weight $1/\varepsilon$ with probability $\varepsilon$ (else $0$) gives the prophet $2 - \varepsilon$ and the gambler at most $1$.

## Depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Sources

- Robert Kleinberg, S. Matthew Weinberg, "Matroid Prophet Inequalities", STOC (2012); Games and Economic Behavior 113 (2019), arXiv:1201.4764, Sections 2 and 3.
