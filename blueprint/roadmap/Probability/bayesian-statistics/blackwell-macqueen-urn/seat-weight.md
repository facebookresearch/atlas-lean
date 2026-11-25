# Seating probabilities in the Chinese restaurant process

For a real number $\theta$ and a set partition $\pi$ of the first $n$ customers $\{0, \dots, n-1\}$, the weight of a [seating choice](seat.md) of customer $n$ is $\theta/(n + \theta)$ for a new table and $|B|/(n + \theta)$ for the table $B$, with the convention that division by $0$ gives $0$. For $\theta > 0$ the weights are [nonnegative](seat-weight-nonneg.md) and [sum to one](sum-seat-weight.md), so they are the seating probabilities of the Chinese restaurant process.
