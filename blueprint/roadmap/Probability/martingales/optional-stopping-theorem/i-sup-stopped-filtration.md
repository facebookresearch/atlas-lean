# The stopped filtration generates the stopping-time σ-algebra

Let
$(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration on a measurable space $\Omega$ and let $\tau$
be a stopping time for it with values in $\mathbb{N} \cup \{\infty\}$. For each $n$, let
$\mathcal{F}_{\tau \wedge n}$ be the σ-algebra of the stopping time $\tau \wedge n$, the $n$-th
σ-algebra of the stopped filtration, and let $\mathcal{F}_\tau$ be the σ-algebra of $\tau$. Then
$\bigvee_n \mathcal{F}_{\tau \wedge n} = \mathcal{F}_\tau$.

The inclusion $\le$ is monotonicity. For $\ge$, a set $s \in \mathcal{F}_\tau$ splits into its
finite-time part $s \cap \{\tau < \infty\} = \bigcup_n (s \cap \{\tau \le n\})$ and its
infinite-time part $s \cap \{\tau = \infty\}$, and both are measurable for the supremum.
