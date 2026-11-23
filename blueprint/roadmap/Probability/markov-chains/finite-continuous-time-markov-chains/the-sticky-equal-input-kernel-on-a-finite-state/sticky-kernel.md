# Sticky kernel

For $\pi : S \to \mathbb{R}$ and a persistence $c \in \mathbb{R}$, the sticky kernel is the
$S \times S$ matrix

$$K_\pi(c) = c\, I + (1 - c)\, \mathbf 1 \pi^\top,$$

where $\mathbf 1 \pi^\top$ is the [equal-input matrix](equal-input.md). For a probability vector
$\pi$ and $0 \le c \le 1$, the chain started from $i$ stays at $i$ with probability $c$ and
otherwise redraws its state from $\pi$.
