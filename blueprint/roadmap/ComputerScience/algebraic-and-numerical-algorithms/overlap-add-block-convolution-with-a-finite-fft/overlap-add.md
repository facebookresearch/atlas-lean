# Overlap-add

Let $Q \ge 1$, $N$, $L$ and $M$ be natural numbers, $x$ a signal of length $N$ and $h$ a kernel of length $M$. The overlap-add output with FFT size $Q$ and hop $L$ is $y : \mathbb{N} \to \mathbb{C}$,

$$y(n) = \sum_{\substack{b < B(N, L) \\ bL \le n}} F_b(n - bL),$$

where $B(N, L)$ is the [block count](block-count.md) and $F_b$ is the [frame](block-frame.md) of block $b$: each frame is shifted to its block start $bL$ and the frames are added.
