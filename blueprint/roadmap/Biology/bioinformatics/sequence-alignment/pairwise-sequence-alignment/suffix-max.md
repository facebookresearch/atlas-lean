# Suffix maximum of Needleman–Wunsch scores

Given a substitution score $\sigma$ and an
integer gap score $g$, the suffix maximum of lists $xs$ and $ys$ is the maximum of the
Needleman–Wunsch scores of all pairs $(u, v)$ with $u$ a suffix of $xs$ and $v$ a suffix of
$ys$.

The maximum is taken with floor $0$, which changes nothing, since the pair of empty suffixes
scores $0$.
