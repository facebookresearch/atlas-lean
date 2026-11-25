# Best-response (support) condition

In a finite game with finitely many players and nonempty finite pure-strategy sets, a mixed profile $\sigma$ is a
[Nash equilibrium](nash-s-theorem/is-mixed-nash.md) if and only if, for every player $i$, every pure strategy in the support of $\sigma_i$
maximizes $i$'s [expected payoff](nash-s-theorem/expected-payoff.md) against $\sigma_{-i}$ among all pure strategies. For a bimatrix game
$(A, B)$ with the row player receiving $x^{\mathsf T} A y$ and the column player $x^{\mathsf T} B y$, $(x, y)$ is a
[Nash equilibrium](bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md) if and only if $x_k > 0$ implies
$(Ay)_k = \max_l (Ay)_l$ and $y_k > 0$ implies $(B^{\mathsf T} x)_k = \max_l (B^{\mathsf T} x)_l$. The reason is that
$U_i(\tau, \sigma_{-i}) = \sum_a \tau(a)\, U_i(a, \sigma_{-i}) \le \max_a U_i(a, \sigma_{-i})$ for every mixed strategy $\tau$ of $i$, with
equality exactly when $\tau$ puts no weight on a non-maximizing pure strategy.

## Depends on

- [Expected payoff of a mixed profile](nash-s-theorem/expected-payoff.md)
- [Mixed Nash equilibrium](nash-s-theorem/is-mixed-nash.md)
- [Expected payoffs in a bimatrix game](bimatrix-games-and-the-lemke-howson-algorithm/bilin-payoff.md)
- [Nash equilibrium of a bimatrix game](bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Related topics

- [Pure best responses of player 1](bimatrix-games-and-the-lemke-howson-algorithm/best-responses.md)
- [Pure best responses of player 2](bimatrix-games-and-the-lemke-howson-algorithm/best-responses-2.md)
- [Correctness of support enumeration for bimatrix games](bimatrix-games-and-the-lemke-howson-algorithm/correctness-of-support-enumeration-for-bimatrix-games.md)

## Sources

- R. Savani and B. von Stengel, *Hard-to-Solve Bimatrix Games*, Econometrica 74 (2006), 397–429, §2, Lemma 1 (attributed there to Nash 1951), stated for one player of a bimatrix game; the $n$-player form follows by the same argument, since $U_i$ is linear in $\sigma_i$. <http://www.maths.lse.ac.uk/Personal/stengel/TEXTE/savanistengel.pdf>
