# Hawk–Dove game: the evolutionarily stable strategy

In the symmetric Hawk–Dove game with value $V > 0$ and cost $C > 0$, the payoff to the row player is $(V - C)/2$ for Hawk against Hawk, $V$ for Hawk against Dove, $0$ for Dove against Hawk and $V/2$ for Dove against Dove (Chicken article, section Hawk–dove). A strategy $p$ is evolutionarily stable if for every $q \ne p$ either $E(p, p) > E(q, p)$, or $E(p, p) = E(q, p)$ and $E(p, q) > E(q, q)$ (Maynard Smith 1974, eq. (1); Haigh's appendix, (A1)–(A2)). (i) If $C > V$, no pure strategy is an ESS, and the unique ESS plays Hawk with probability $V/C$. (ii) If $V \ge C$, pure Hawk is the unique ESS. The derivation: for $C > V$, Dove is invaded by Hawk ($V > V/2$) and Hawk by Dove ($0 > (V - C)/2$); the equal-payoff condition $p\,(V - C)/2 + (1 - p)V = (1 - p)V/2$ gives $p = V/C$, and for this $p$ and any $q \ne p$, $E(p, q) - E(q, q) = -(p - q)\cdot A(p - q) = \frac{C}{2}(p_H - q_H)^2 > 0$, using $(p - q)\cdot Ap = 0$; this is Haigh's 2-by-2 formula $p = (b - c)/(a + b - c)$ after the normalization of his Theorem 2. For $V > C$ Hawk is strict; for $V = C$, $E(H, H) = E(D, H) = 0$ and $E(H, D) = V > E(D, D) = V/2$.

## Expansion

1. Symmetric two-strategy games, mixed strategies and the ESS conditions.
2. The equal-payoff computation $p = V/C$.
3. The second-order condition: $(q - p)\cdot A(q - p) = -\frac{C}{2}(q_H - p_H)^2 < 0$ for $C > V$, so the mixed strategy is an ESS and no pure strategy is.
4. The case $V \ge C$.
5. Convergence of the replicator dynamics of the game to the ESS from every interior state, as a separate statement.

## Sources

- Chicken (game), Wikipedia, section Hawk–dove. <https://en.wikipedia.org/wiki/Chicken_(game)>
- J. Maynard Smith, The theory of games and the evolution of animal conflicts, J. Theor. Biol. 47 (1974), 209–221, Sec. 2, eq. (1), and the appendix by J. Haigh, (A1)–(A2) and Theorem 2. <https://doi.org/10.1016/0022-5193(74)90110-6>
- Original result: J. Maynard Smith and G. R. Price, The logic of animal conflict, Nature 246 (1973), 15–18. <https://doi.org/10.1038/246015a0> The Hawk–Dove game follows the Chicken article.
