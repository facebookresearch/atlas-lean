# Sigma rule for strategy selection under weak selection

Consider two strategies $A$ and $B$ with payoff matrix

$$\begin{array}{c|cc} & A & B \\ \hline A & R & S \\ B & T & P \end{array}$$

($R$: payoff of $A$ against $A$; $S$: $A$ against $B$; $T$: $B$ against $A$; $P$: $B$ against $B$). Consider a finite population with a fixed structure and an update rule that is symmetric in the two strategies and depends on payoffs only through fitness $1 + w\cdot\text{payoff}$, with mutation between strategies. Then, in the limit of weak selection $w \to 0$, there is a number $\sigma$ depending on the population structure, the update rule and the mutation rate, but not on $R, S, T, P$, such that $A$ is more abundant than $B$ in the mutation–selection equilibrium if and only if

$$\sigma R + S \ >\ T + \sigma P .$$

Examples:

- well-mixed population of size $N$: $\sigma = (N-2)/N$, which tends to $1$ as $N \to \infty$, recovering risk dominance $R + S > T + P$;
- large $k$-regular graph with death–birth updating: $\sigma = (k+1)/(k-1)$.

$\sigma > 1$ means the structure favours the diagonal entries, i.e. interactions with the same strategy, which is the effect of spatial or network clustering.

## Depends on

- [Moran fixation probability](../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Expansion

Under weak selection the condition for $A$ to be favoured is linear in the payoffs, so it can be written as $k_1R + k_2S > k_3T + k_4P$ with structural coefficients $k_i$. Symmetry of the update rule (relabelling $A \leftrightarrow B$ swaps $R \leftrightarrow P$ and $S \leftrightarrow T$) and the fact that adding a constant to all payoffs changes nothing at first order force the condition into the form $\sigma(R - P) > T - S$. Because $\sigma$ is independent of the payoffs, it can be computed once for a structure, for example from any simple game whose outcome is known, and then applied to every two-strategy game.

## Sources

- M. A. Nowak, C. E. Tarnita, T. Antal, "Evolutionary dynamics in structured populations", Philosophical Transactions of the Royal Society B 365 (2010) 19–30, <https://doi.org/10.1098/rstb.2009.0215> (PMC2842709).
- C. E. Tarnita, H. Ohtsuki, T. Antal, F. Fu, M. A. Nowak, "Strategy selection in structured populations", Journal of Theoretical Biology 259 (2009) 570–581, <https://doi.org/10.1016/j.jtbi.2009.03.035>.
