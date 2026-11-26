# Five-species counterexample to the Hofbauer-Kon-Saito conjecture

**Theorem.** Let
$$A = \begin{pmatrix} -1 & 1 & 2 & 0 & 0 \\ -2 & -2 & 0 & 12 & 0 \\ -1 & 0 & -1 & 0 & 0 \\ 0 & 0 & 0 & -1 & -24 \\ 0 & 12 & 0 & 0 & -1 \end{pmatrix}, \qquad r = (1, 3, 3, 1, -2).$$

1. $a_{ii} < 0$ for all $i$, and $A$ satisfies the [cycle conditions (C1) and (C2)](hofbauer-kon-saito-cycle-conditions-for-qualitative-permanence.md).
2. The Lotka-Volterra system $\dot x_i = x_i(r_i + (Ax)_i)$ has an interior equilibrium $x^* \approx (2.390, 0.170, 0.610, 0.177, 0.034)$.
3. The boundary of $\mathbb R^5_{\ge 0}$ contains a heteroclinic cycle $F_{13} \to F_{134} \to F_{124} \to F_{125} \to F_{13}$ through the boundary equilibria $F_{13} = (\tfrac73, 0, \tfrac23, 0, 0)$, $F_{134} = (\tfrac73, 0, \tfrac23, 1, 0)$, $F_{124} = (\tfrac{17}4, \tfrac{13}4, 0, 1, 0)$ and $F_{125} = (\tfrac54, \tfrac14, 0, 0, 1)$.
4. This cycle is asymptotically stable. Hence the system is not permanent and $A$ is not qualitatively permanent.

So (C1) and (C2) are necessary but not sufficient for qualitative permanence when $n = 5$.

**Corollary.** The conjecture fails for every $n \ge 5$: append species with $a_{ii} = -1$, $r_i = 1$ and no interactions.

**Robustness.** For every $n \ge 5$ there is $\varepsilon > 0$ such that every $(\tilde A, \tilde r)$ within $\varepsilon$ entrywise of the padded example, with $\tilde A$ satisfying (C1), has an interior equilibrium and an asymptotically stable boundary heteroclinic cycle through equilibria with the same supports. Consequently, every $n \times n$ sign pattern with negative diagonal that satisfies (C1) and (C2) and contains, after relabeling, the sign pattern of $A$ at its nonzero entries is not qualitatively permanent.

## Depends on

- [Hofbauer-Kon-Saito cycle conditions for qualitative permanence](hofbauer-kon-saito-cycle-conditions-for-qualitative-permanence.md)

## Expansion

Each connection of the cycle lies in a face where the restricted interaction matrix is Volterra-Lyapunov stable, so the face dynamics converge to a single saturated equilibrium; connection lemmas based on invasion rates and invasion graphs then produce the four heteroclinic orbits. Asymptotic stability within the boundary follows because the cycle consists of simple, hyperbolic, internally stable equilibria, and stability in the full orthant follows from the Hofbauer criterion: the characteristic matrix $C$ of invasion rates at the four equilibria admits $p \ll 0$ with $Cp \gg 0$. A stable boundary attractor rules out permanence even though an interior equilibrium exists. All hypotheses are open conditions, which gives robustness and turns the example into a forbidden sign motif. Every counterexample in the sign class of $A$ needs the loop ratio $\ell = |a_{24}a_{45}a_{52}|/|a_{22}a_{44}a_{55}|$ of the negative cycle through species 2, 4 and 5 to be at least $8$; for $\ell < 8$ the matrix is Volterra-Lyapunov stable and the system is permanent (in the example, $\ell = 1728$).

## Sources

- M.-M. Beldiman and A.-D. Halanay, "A five-species counterexample to the Hofbauer-Kon-Saito conjecture on qualitative permanence", arXiv preprint (2026), Theorem 1.2, Corollary 1.3, Theorem 5.1, Corollary 5.2 and Proposition 5.3. <https://doi.org/10.48550/arXiv.2610.38374>