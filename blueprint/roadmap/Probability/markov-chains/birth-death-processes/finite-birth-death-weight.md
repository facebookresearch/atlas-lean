# Unnormalized weights of a finite birth–death chain

For a matrix $Q$ on $\{0,\ldots,K\}$, the weight of state $n$ is

$$w_n = \prod_{i<n} \frac{Q_{i,i+1}}{Q_{i+1,i}}.$$

The empty product gives $w_0=1$. The definition uses the adjacent entries of $Q$ even for a matrix that is not a rate matrix. In Lean, division by zero is defined to be zero; the [stationary law](stationary-law-of-a-finite-birth-death-chain.md) assumes strictly positive downward rates, so no denominator vanishes there.
