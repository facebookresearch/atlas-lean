# The ideal free distribution is an evolutionarily stable state

A single species with total density $M > 0$ distributes over $H$ patches according to $p$ in the simplex $\Delta_H$, and an individual in patch $i$ receives payoff $V_i(p_i M)$, where each $V_i$ is strictly decreasing. With the patches ordered so that $V_1(0) \ge \dots \ge V_H(0)$, the ideal free distribution (IFD) $p^*$ at density $M$ occupies patches $1, \dots, k$ with equal payoffs $V_1(p_1^* M) = \dots = V_k(p_k^* M) = V^* \ge V_{k+1}(0)$, so that no individual can gain by moving (Cressman and Křivan 2006, section "The IFD Is an ESS", p. 386, where the patches are strictly ordered and each $V_i$ has a carrying capacity; neither assumption is used in the proof below). Cressman and Křivan (2006, online Appendix A, inequality (A1)) prove that the IFD is an evolutionarily stable state in the nonlinear sense: for every $p \in \Delta_H$ with $p \ne p^*$,

$$\sum_i p_i^*\, V_i(p_i M) > \sum_i p_i\, V_i(p_i M).$$

When all patches are occupied the proof writes the difference as $\sum_i (p_i^* - p_i)[V_i(p_i M) - V_i(p_i^* M)]$, each term of which is nonnegative and positive unless $p_i = p_i^*$, because $V_i$ is strictly decreasing; the case of unoccupied patches uses $V^* \ge V_i(0)$ for $i > k$.

## Expansion

1. The model: patch payoffs depending on local density, the population state on the simplex, and the definition of the IFD (Fretwell and Lucas).
2. Existence and uniqueness of the IFD under strict monotonicity of the $V_i$.
3. The stability inequality (A1) of the source's online Appendix A, in the two cases $k = H$ and $k < H$.
4. Consequences for distributional dynamics (convergence of migration dynamics to the IFD), as separate statements.

## Sources

- R. Cressman and V. Křivan, Migration dynamics for the ideal free distribution, Am. Nat. 168 (2006), 384–397, section "The IFD Is an ESS" (p. 386, the definition of the IFD and equal payoffs) and online Appendix A, inequality (A1) (the evolutionary-stability inequality and its proof). Author copy with the appendixes: <https://fix.prf.jcu.cz/~krivan/clanky/CressmanKrivan-AmNat-2006all.pdf>. <https://doi.org/10.1086/506970>
- Original result: S. D. Fretwell and H. L. Lucas, On territorial behavior and other factors influencing habitat distribution in birds, Acta Biotheor. 19 (1969), 16–36. <https://doi.org/10.1007/BF01601953> The definition of the ideal free distribution follows Cressman and Křivan (2006).
