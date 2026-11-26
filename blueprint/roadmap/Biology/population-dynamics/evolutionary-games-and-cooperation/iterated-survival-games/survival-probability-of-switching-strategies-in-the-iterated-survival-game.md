# Survival probability of switching strategies in the iterated survival game

**Model.** Two individuals play $n$ steps. In each step both choose $C$ or $D$ and each survives the step independently with probability given by its own behaviour and its partner's: $a$ for $C$ against $C$, $b$ for $C$ against $D$, $c$ for $D$ against $C$, $d$ for $D$ against $D$; an individual whose partner has died survives each remaining step with the loner probability $a_0$. All five parameters lie in $(0,1)$, are fixed over the game, and $a > d$. Strategy $S_i$ plays $C$ for the first $n-i$ steps and $D$ for the last $i$ steps ($S_0$ is all-$C$, $S_n$ all-$D$). The payoff $A(S_j; S_i)$ is the probability that an individual playing $S_j$ against a partner playing $S_i$ is alive after step $n$.

**Theorem.** For $j \ge i$,

$$\begin{aligned}
A(S_j;S_i) ={}& a^{2(n-j)}(bc)^{j-i}d^{2i}
+ a(1-a)\,a_0^{\,j}\,\frac{a_0^{\,n-j}-a^{2(n-j)}}{a_0-a^2} \\
&+ c(1-b)\,a^{2(n-j)}a_0^{\,i}\,\frac{a_0^{\,j-i}-(bc)^{j-i}}{a_0-bc}
+ d(1-d)\,a^{2(n-j)}(bc)^{j-i}\,\frac{a_0^{\,i}-d^{2i}}{a_0-d^2},
\end{aligned}$$

and for $j \le i$ the same formula holds with $b$ and $c$ exchanged and $i$ and $j$ exchanged. Each quotient denotes the corresponding finite geometric sum, so the formula is defined for all parameter values. In particular, against a fully cooperative partner,

$$A(S_j;S_0) = \frac{a-a^2}{a_0-a^2}\,a_0^{\,n} + a^{2n}\left[\frac{a_0-c}{a_0-bc}\Big(\frac{bc}{a^2}\Big)^{j} + \Big(\frac{c-bc}{a_0-bc}-\frac{a-a^2}{a_0-a^2}\Big)\Big(\frac{a_0}{a^2}\Big)^{j}\right],$$

which does not depend on $d$.

## Proof sketch

Track one individual through the states (alive with partner, alive alone, dead). For a pair of behaviours $XY$ the one-step transition matrix is upper triangular with diagonal entries equal to the pair survival probability ($a^2$, $bc$ or $d^2$), $a_0$ and $1$; these are its eigenvalues, and diagonalizing gives closed-form matrix powers, for example the first row of $A_{CC}^k$ is $\big(a^{2k},\ a(1-a)\frac{a_0^k - a^{2k}}{a_0-a^2},\ \cdot\big)$. For $j \ge i$ the game is the product $A_{CC}^{\,n-j}A_{DC}^{\,j-i}A_{DD}^{\,i}$, and $A(S_j;S_i)$ is the sum of the first two entries of its first row. The four terms are the four disjoint ways to survive: the partner also survives the whole game, or the partner dies during the $CC$, the mixed, or the $DD$ phase, after which the individual survives alone at rate $a_0$. In the mixed phase the individual (playing $D$) survives with probability $c$ while its cooperating partner dies with probability $1-b$, giving the factor $c(1-b)$. Setting $i = 0$ removes the $DD$ phase and yields the formula against $S_0$; note that $n$ and $j$ separate, so the optimal $j$ against $S_0$ is independent of $n$ once $n$ is large enough.

## Sources

- O. Salagnac and J. Wakeley, "The consequences of switching strategies in a two-player iterated survival game", Journal of Mathematical Biology 82 (2021), Sect. 2 "Markov model of individual survival and preliminary calculations", Eqs. (6)–(14), <https://doi.org/10.1007/s00285-021-01569-3>, PMCID PMC7867574.
