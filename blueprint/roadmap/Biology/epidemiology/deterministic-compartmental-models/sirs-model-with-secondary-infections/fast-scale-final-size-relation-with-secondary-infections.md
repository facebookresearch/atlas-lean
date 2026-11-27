# Fast-scale final-size relation with secondary infections

**Setting.** In the SIRS model with secondary infections, let $\varepsilon \to 0$ (immunity waning much slower than infection). The fast limit system is

$$
S' = -\beta S (I + \alpha Y),\quad I' = \beta S(I + \alpha Y) - \gamma_1 I,\quad T' = \gamma_1 I,\quad P' = -\nu\beta P(I + \alpha Y),\quad Y' = \nu\beta P(I + \alpha Y) - \gamma_2 Y,
$$

and its equilibria form the critical set $\mathcal{C}_1 = \{I = Y = 0\}$.

**Result.** Every trajectory of the fast system converges to $\mathcal{C}_1$. Starting from $(S_0, I_0, T_0, P_0, Y_0)$ with $S_0 > 0$, the limit $S_\infty$ is the unique solution in $(0, S_0)$ of

$$
\log\frac{S_\infty}{S_0} - \beta\left(\frac{S_\infty - S_0}{\gamma_1} + \alpha\,\frac{P_0 (S_\infty / S_0)^{\nu} - P_0}{\gamma_2}\right) = -\beta\left(\frac{I_0}{\gamma_1} + \alpha\,\frac{Y_0}{\gamma_2}\right),
$$

and the partially susceptible pool ends at

$$
P_\infty = P_0 \left(\frac{S_\infty}{S_0}\right)^{\nu}.
$$

## Depends on

- [Equilibria and backward bifurcation of the SIRS model with secondary infections](equilibria-and-backward-bifurcation-of-the-sirs-model-with-secondary-infections.md)
- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Proof sketch

Both susceptible classes are depleted by the same force of infection $\lambda = \beta(I + \alpha Y)$, so $(\log P)' = \nu (\log S)'$ and $P / P_0 = (S/S_0)^{\nu}$ along orbits. Integrating $I' + Y'$ and using $\int_0^\infty \lambda\,dt = -\log(S_\infty/S_0)$ gives the implicit equation, which reduces to the Kermack–McKendrick final-size equation when $P_0 = Y_0 = 0$. In the full three-scale system this relation is the "entry" map of the slow–fast cycle: it determines where an outbreak lands on $\mathcal{C}_1$, and hence whether the next outbreak starts on the intermediate time scale or only after slow loss of protection.

## Sources

- Panagiotis Kaklamanos, Andrea Pugliese, Mattia Sensi and Sara Sottile, "A Geometric Analysis of the SIRS Model with Secondary Infections", *SIAM Journal on Applied Mathematics* 84 (2024), 661–686, <https://doi.org/10.1137/23m1565632>. Preprint version: arXiv:2304.03793 (2023), Section 4, Proposition 6 and Lemma 7, <https://doi.org/10.48550/arXiv.2304.03793>.
