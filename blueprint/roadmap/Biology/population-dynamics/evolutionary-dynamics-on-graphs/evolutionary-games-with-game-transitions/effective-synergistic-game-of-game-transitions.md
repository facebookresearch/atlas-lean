# Effective synergistic game induced by game transitions

Consider the two-state game-transition model on a large $k$-regular graph under death–birth updating and weak selection: two donation games with benefits $b_1 > b_2 > c$ and common cost $c$, where mutual cooperation leads to game $1$ and every other outcome leads to game $2$. The condition for cooperators to be favored,

$$\frac{b_1}{c} > k - \frac{k-1}{2}\,\frac{b_1 - b_2}{c},$$

is exactly the sigma rule $\sigma R + S > T + \sigma P$ with the large-graph death–birth structure coefficient $\sigma = (k+1)/(k-1)$ applied to the single effective game

$$R = b_1 - c + (b_1 - b_2)\,\frac{k-1}{k+1}, \qquad S = -c, \qquad T = b_1, \qquad P = 0 .$$

Compared with the donation game with benefit $b_1$, each of two mutual cooperators receives an extra synergistic payoff $(b_1 - b_2)(k-1)/(k+1)$. The game transitions therefore act like partner-fidelity feedback: one's cooperation keeps the shared interaction in the valuable state, and this benefit returns to the cooperator. The extra term is of order $b_1 - b_2$ rather than $(b_1 - b_2)/k$, which is why a small difference between games can sharply lower the threshold for cooperation on highly connected networks.

## Depends on

- [Critical benefit-to-cost ratio with game transitions](critical-benefit-to-cost-ratio-with-game-transitions.md)

## Proof sketch

Substitute $\sigma = (k+1)/(k-1)$ and the effective payoffs into $\sigma R + S > T + \sigma P$:

$$\frac{k+1}{k-1}(b_1 - c) + (b_1 - b_2) - c > b_1 .$$

Multiplying by $(k-1)/2$ gives $b_1 - kc + \frac{k-1}{2}(b_1 - b_2) > 0$, which is the death–birth game-transition condition with $\xi = (k-1)/2$. Because the sigma coefficient does not depend on payoffs, the whole effect of the environment's feedback is absorbed into a shift of the reward $R$.

## Sources

- Q. Su, A. McAvoy, L. Wang, M. A. Nowak, "Evolutionary dynamics with game transitions", Proceedings of the National Academy of Sciences USA 116(51) (2019) 25398–25404, Eq. 1 and Discussion, <https://doi.org/10.1073/pnas.1908936116> (PMC6926053).
