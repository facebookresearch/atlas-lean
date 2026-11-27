# Shortest vector, independent vectors and guaranteed distance decoding problems

For a lattice $L$ given by a basis and an approximation factor $\gamma \ge 1$: $\mathrm{SVP}_\gamma$ asks for a nonzero lattice vector of norm at most $\gamma\lambda_1(L)$; $\mathrm{SIVP}_\gamma$ asks for $n$ linearly independent lattice vectors of norm at most $\gamma\lambda_n(L)$; the *generalized independent vectors problem* $\mathrm{GIVP}^{\phi}_\gamma$ replaces $\lambda_n$ by an arbitrary lattice function $\phi$; and the *guaranteed distance decoding* problem $\mathrm{GDD}^{\phi}_\gamma$ asks, for a target $t$, for a lattice vector within distance $\gamma\,\phi(L)$ of $t$. For $g > 0$, the *incremental* guaranteed distance decoding problem $\mathrm{IncGDD}^{\phi}_{\gamma,g}$ is given, besides the basis and a target $t$, a set $S$ of $n$ linearly independent vectors of $L$ and a real $r > \gamma\,\phi(L)$, and asks for a lattice vector $s$ with $\|s - t\| \le \|S\|/g + r$, where $\|S\| = \max_i \|s_i\|$; write $\mathrm{IncGDD}^{\phi}_{\gamma}$ for $\mathrm{IncGDD}^{\phi}_{\gamma,8}$.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
- D. Micciancio and S. Goldwasser, "Complexity of Lattice Problems: A Cryptographic Perspective", Springer, 2002.
