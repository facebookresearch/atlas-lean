# Support characterization of mixed best responses

In a finite game, fix a mixed profile $\sigma_{-i}$ of the other players and let $U(a) = u_i(a, \sigma_{-i})$ be player $i$'s expected payoff from each pure action $a$. A mixed strategy $\sigma_i$ is a best response to $\sigma_{-i}$ if and only if every pure action in its support attains $\max_a U(a)$. In particular a best response may mix arbitrarily among maximizing actions, including when several are tied, and the set of best responses is the face of the simplex spanned by the maximizers. Proof: $u_i(\sigma_i, \sigma_{-i}) = \sum_a \sigma_i(a)U(a) \le \max_a U(a)$, with equality exactly when $\sigma_i$ puts no weight on a non-maximizer.

## Proof depends on

- [Mixed Nash equilibrium](is-mixed-nash.md): expected payoffs of mixed profiles.

## Sources

- N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Section 2.1.1, Theorem 2.1, <https://www.cs.cmu.edu/~sandholm/cs15-892F13/algorithmic-game-theory.pdf>
