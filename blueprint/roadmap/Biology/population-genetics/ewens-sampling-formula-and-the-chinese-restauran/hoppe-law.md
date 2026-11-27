# Law of the allelic partition from Hoppe's urn

For a real number $\theta$, the weights $h_n(\pi)$ on the integer partitions $\pi$ of $n$ are defined recursively: $h_0$ gives weight $1$ to the empty partition, and

$$h_{n+1}(\pi') = \sum_{\pi} h_n(\pi)\, t(\pi, \pi'),$$

the sum running over the integer partitions $\pi$ of $n$, with the [transition weights of Hoppe's urn](hoppe-step.md) $t$. For $\theta > 0$, $h_n$ is the law of the allelic partition after $n$ draws from Hoppe's urn started from the empty sample.
