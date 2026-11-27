# Donsker's invariance principle in the Skorokhod space D([0,1])

Let $X_0, X_1, \dots$ be i.i.d. measurable real random variables on a probability space with mean $0$ and variance $1$, and let $B$ be a real Brownian motion on a probability space. Then there is a continuous version $Y$ of $B$ on $[0, 1]$ ($Y_t = B_t$ for all $t$, almost surely) such that the normalized partial-sum step processes $t \mapsto n^{-1/2} \sum_{i < \lfloor n t\rfloor} X_i$ converge in distribution to $Y$ in the Skorokhod space $D([0, 1])$ with the J1 topology.

The proof combines Donsker's theorem in $C([0, 1])$ for the polygonal process, the sup-distance bound $\sup_t |\text{step} - \text{polygon}| \le \max_{i<n} |X_i|/\sqrt n$, which tends to $0$ in probability, and tightness of the polygonal laws.

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999), §14 ("Donsker's Theorem Again", p. 146), Donsker's theorem in $D[0,1]$; proof route through Theorem 8.2 (Donsker in $C$) and Theorem 3.1 (converging together).
