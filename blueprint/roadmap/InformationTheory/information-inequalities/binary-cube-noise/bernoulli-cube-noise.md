# Binary-cube bit noise and the sign-convention noise operator

The input of length $n$ is uniform on Boolean words. For $0\le\varepsilon\le1/2$ flip each bit independently with probability $\varepsilon$; the conditional output mass at $y$ given $x$ is the product of the relevant flip and no-flip factors. In the $\{\pm1\}$ convention the noise operator $T_\rho$ is defined for every $-1\le\rho\le1$: each coordinate is retained with probability $(1+\rho)/2$ and otherwise negated, independently. It maps a function to its conditional average after this noise. The flip range used above corresponds to $\rho=1-2\varepsilon\ge0$. A Boolean-valued statistic is obtained by a function of the original input. For a real-valued profile $-1\le u\le1$, a randomized sign has conditional probability $(1+u(x))/2$ of $+1$ given $x$. Mutual information is computed from the finite joint mass and its marginals, with zero atoms contributing zero; use nats before any division by $\log2$.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CourtadeKumar.lean#L7-L53)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SoftChannel204.lean#L11-L72)
