# Reverse Minkowski theorem

Let $\mathcal{L} \subseteq \mathbb{R}^n$ be a full-rank lattice, that
is, a discrete subgroup of $\mathbb{R}^n$ that spans $\mathbb{R}^n$, such that every subgroup
$\mathcal{L}' \subseteq \mathcal{L}$ (a lattice of possibly lower rank) has determinant
$\det(\mathcal{L}') \ge 1$. Let $t = 10(\log n + 2)$, where $\log$ is the natural logarithm. Then
the Gaussian mass of $\mathcal{L}$ at parameter $1/t$ satisfies
$\rho_{1/t}(\mathcal{L}) = \sum_{y \in \mathcal{L}} e^{-\pi t^2 \|y\|^2} \le 3/2$, where
$\|y\|$ is the Euclidean norm.

## Sources

- O. Regev, N. Stephens-Davidowitz, `A reverse Minkowski theorem`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_reverse_minkowski` of the lean-eval benchmark.
