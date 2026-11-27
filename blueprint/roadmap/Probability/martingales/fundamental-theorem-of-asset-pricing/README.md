# One-period fundamental theorem of asset pricing

Let $\Omega$ be a nonempty finite set of states and $A$ a finite set of assets, and let $g(a, \omega) \in \mathbb{R}$ be the gain of asset $a$ in state $\omega$. A portfolio $h : A \to \mathbb{R}$ is an arbitrage if its gain $\sum_{a \in A} h(a)\, g(a, \omega)$ is nonnegative in every state and positive in some state. There is no arbitrage if and only if there is a probability $q$ on $\Omega$ with $q(\omega) > 0$ for every state $\omega$ under which every asset has zero expected gain: $\sum_{\omega \in \Omega} q(\omega)\, g(a, \omega) = 0$ for every $a \in A$.

## Idea

The theorem turns an economic condition, no riskless profit, into a probabilistic one: a strictly positive "risk-neutral" probability under which every gain has mean zero, so that prices are fair in expectation. One direction is immediate: if such a $q$ exists and a portfolio's gain is nonnegative, its $q$-expectation is $0$, and since every $q(\omega) > 0$ the gain vanishes in every state. The other direction is a separation argument in $\mathbb{R}^\Omega$: without arbitrage, the linear space of portfolio gains does not meet the compact convex set of probability vectors, so a hyperplane through the origin containing that space separates them, and its normal vector, normalised, is $q$. In multi-period markets the same idea makes discounted prices martingales under $q$, which is the basis of arbitrage-free pricing of derivatives.

## Statements

- [One-period fundamental theorem of asset pricing](one-period-fundamental-theorem-asset-pri-2.md)
- [Fundamental theorem of asset pricing for a finite one-period market](one-period-fundamental-theorem-asset-pri.md): the same statement without decidability assumptions on the index sets; the main statement is derived from it
- [Conditional one-period fundamental theorem of asset pricing](conditional-one-period-ftap.md)
- [Dalang–Morton–Willinger theorem](dalang-morton-willinger-theorem.md)
- [The Delbaen–Schachermayer fundamental theorem of asset pricing](delbaen-schachermayer-ftap.md)

## Sources

- J. M. Harrison and D. M. Kreps, "Martingales and arbitrage in multiperiod securities markets", *Journal of Economic Theory* (1979).
- H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, de Gruyter.
