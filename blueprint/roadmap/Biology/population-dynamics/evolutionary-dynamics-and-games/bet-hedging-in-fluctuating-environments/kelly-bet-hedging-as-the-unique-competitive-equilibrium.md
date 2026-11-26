# Kelly bet-hedging as the unique competitive equilibrium

Environments $X_1, X_2, \dots$ are i.i.d. with $P(X = i) = p_i$, $i = 1, \dots, k$. A lineage produces phenotype $j$ with probability $f_j$, $f \in \Delta^{k-1}$, and phenotype $j$ has fitness $o_{ij} \ge 0$ in environment $i$, with $o_{ii} > o_{ij}$ and $o_{ii} > 1$. Writing $\bar o_i(f) = \sum_j o_{ij} f_j$ and $H \sim \mathrm{Multinomial}(n, p)$ for the environment counts, the lineage size after $n$ generations is

$$W_n(f) = \prod_{i=1}^k \bar o_i(f)^{H_i}, \qquad G(f) := \lim_{n\to\infty} W_n(f)^{1/n} = \prod_{i=1}^k \bar o_i(f)^{p_i} \ \text{a.s.}$$

The **Kelly strategy** $f_{\mathrm{Kelly}}$ maximizes $G$ (equivalently $E\log W_1$) over the simplex. For $k = 2$ with $f = f_1$,

$$f_{\mathrm{Kelly}}(p) = \frac{(1-p)\,o_{12}}{o_{12} - o_{11}} + \frac{p\,o_{22}}{o_{22} - o_{21}} \quad \text{for } p \in [p_-, p_+],$$

with $f_{\mathrm{Kelly}} = 0$ for $p \le p_-$ and $f_{\mathrm{Kelly}} = 1$ for $p \ge p_+$, where $p_\pm$ are the values at which the linear expression equals $0$ and $1$; the interval $[p_-, p_+]$ is the bet-hedging region.

**Competitive game ($k = 2$).** Two lineages with strategies $f$ and $g$ experience the same environments and have independent initial sizes $W_0, V_0$ with a common uniform distribution (fair randomization). The payoff is $M_n(f,g) = P(W_0 W_n(f) > V_0 W_n(g))$.

**Theorem.**
1. $E[W_n(f)/W_n(f_{\mathrm{Kelly}})] \le 1$ for all $f$, with equality for all $f$ exactly when $p_- < p < p_+$.
2. For every horizon $n$, $M_n(f, f_{\mathrm{Kelly}}) < \tfrac12 = M_n(f_{\mathrm{Kelly}}, f_{\mathrm{Kelly}})$ for all $f \ne f_{\mathrm{Kelly}}$, so $(f_{\mathrm{Kelly}}, f_{\mathrm{Kelly}})$ is a strict Nash equilibrium.
3. It is the unique Nash equilibrium, because $M_n(f,g) + M_n(g,f) \le 1$.
4. The same holds, for every target size $c$, for the payoff "reach lineage size $c$ first", and Kelly remains the static equilibrium when environments are independent but not identically distributed.

Without fair randomization, the best response $\arg\max_f P(W_n(f) > W_n(g))$ depends on $g$ and $n$ and need not be Kelly.

## Expansion

Conditionally on $s$ environments of type 1, $W_n(f)/W_n(g) = \alpha_1^s \alpha_2^{n-s}$ with $\alpha_i = \bar o_i(f)/\bar o_i(g)$, so $E[W_n(f)/W_n(g)] = (p\alpha_1 + (1-p)\alpha_2)^n$, and the first-order condition for $f_{\mathrm{Kelly}}$ makes $p\alpha_1 + (1-p)\alpha_2 \le 1$ when $g = f_{\mathrm{Kelly}}$. For independent uniform initial sizes, $P(r W_0 > V_0) = r/2$ when $r \le 1$ and $1 - 1/(2r)$ when $r > 1$. Both are at most $r/2$, strictly so for $r > 1$, so $M_n(f, f_{\mathrm{Kelly}}) < \tfrac12 E[W_n(f)/W_n(f_{\mathrm{Kelly}})] \le \tfrac12$; this is the Bell–Cover competitive-optimality argument transferred to lineage growth. Uniqueness follows because any other equilibrium would give $M_n(f_0,g_0) + M_n(g_0,f_0) > 1$. Over long horizons the payoff matrix converges to the ordering by $G$, recovering Kelly's asymptotic dominance. Fair randomization of initial size thus explains why Kelly is optimal both asymptotically and at every finite horizon.

## Sources

- O. Tal, T. D. Tran, "Adaptive bet-hedging revisited: considerations of risk and time horizon", Bulletin of Mathematical Biology (2020), Eqs. (2)–(5), Appendix A, Appendices G–J (Propositions 1–6) and Appendix M, <https://doi.org/10.1007/s11538-020-00729-8>, PMCID PMC7128013.
