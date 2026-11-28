# Deviation of a scaled count path from a real path

Let $S$ be a finite set of species. For a natural number $N$, a count path
$X \colon \mathbb{R} \to \mathbb{N}^S$, a real path $x \colon \mathbb{R} \to \mathbb{R}^S$ and a
time $t \in \mathbb{R}$, the deviation at time $t$ is the [ℓ¹ distance](l1-norm.md) between the
[scaled state](scaled.md) $X(t)/N$ and $x(t)$:

$$D(t) = \left\|X(t)/N - x(t)\right\|_1 = \sum_{i \in S} \left|X(t)_i/N - x(t)_i\right|.$$

It is meant for $N \ge 1$; for $N = 0$ the convention $a/0 = 0$ gives $D(t) = \|x(t)\|_1$.
