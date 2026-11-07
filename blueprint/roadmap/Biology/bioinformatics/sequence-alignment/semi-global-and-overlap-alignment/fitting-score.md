# Fitting score

Let $\sigma$ be a substitution score and $g$ a gap score. The fitting
score of a sequence $x$ against a sequence $y$ is the maximum, over all infixes $l$ of $y$
(including the empty one), of the Needleman–Wunsch score of $x$ against $l$ with $\sigma$ and
$g$: the best global alignment score of $x$ against a substring of $y$.

The empty infix is always a candidate, so the maximum is attained. Unlike the overlap score,
the fitting score is not floored at $0$: it can be negative when every fitting alignment
scores negatively.
