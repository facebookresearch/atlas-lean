# Partner conditions for reactive-2 and reactive-3 strategies

In the infinitely repeated donation game (cooperation costs $c > 0$ and gives the co-player $b > c$), let $p = (p_h)$ be a reactive-$n$ strategy, with $p_h$ the cooperation probability after the co-player's last $n$ moves $h$ (oldest first).

**Reactive-2.** $p = (p_{CC}, p_{CD}, p_{DC}, p_{DD})$ is a partner (nice and a Nash equilibrium) if and only if

$$p_{CC} = 1, \qquad \frac{p_{CD} + p_{DC}}{2} \le 1 - \frac{1}{2}\cdot\frac{c}{b}, \qquad p_{DD} \le 1 - \frac{c}{b}.$$

The partners form a three-dimensional polyhedron. It suffices to test two deviations: strict alternation between $C$ and $D$ (second inequality) and ALLD (third). The timing of a single defection in memory does not matter; only the average of $p_{CD}$ and $p_{DC}$ is constrained.

**Reactive-3.** $p$ is a partner if and only if $p_{CCC} = 1$ and

$$\begin{aligned}
\frac{p_{CDC} + p_{DCD}}{2} &\le 1 - \frac{1}{2}\cdot\frac{c}{b}, &
\frac{p_{CCD} + p_{CDC} + p_{DCC}}{3} &\le 1 - \frac{1}{3}\cdot\frac{c}{b}, \\
\frac{p_{CDD} + p_{DCD} + p_{DDC}}{3} &\le 1 - \frac{2}{3}\cdot\frac{c}{b}, &
\frac{p_{CCD} + p_{CDD} + p_{DCC} + p_{DDC}}{4} &\le 1 - \frac{1}{2}\cdot\frac{c}{b}, \\
p_{DDD} &\le 1 - \frac{c}{b}. &&
\end{aligned}$$

The five inequalities correspond to the deviations that repeat $CD$, $CCD$, $CDD$, $CCDD$ and $D$. In every case the bound on the average cooperation probability drops by $c/b$ times the fraction of defections in the repeated sequence: for each defection in memory, cooperation must be diminished proportionally.

These conditions are specific to the donation game; for a general prisoner's dilemma more inequalities are needed. Since reactive-2 strategies are reactive-3 strategies that ignore the oldest move, the reactive-2 conditions are a special case of the reactive-3 ones.

## Depends on

- [Self-reactive best responses to reactive-n strategies](self-reactive-best-responses-to-reactive-n-strategies.md)

## Proof sketch

By the self-reactive reduction, a nice $p$ is a partner iff no deterministic self-reactive-$n$ strategy beats the mutual-cooperation payoff $b - c$ against it. A deterministic self-reactive strategy enters a cycle that repeats a fixed word; against the repeated word $CD$ (for $n = 2$), in each round in which the deviator defects its last two moves were $D$ then $C$, so it receives $b$ with probability $p_{DC}$ without paying, and in each round in which it cooperates it receives $b$ with probability $p_{CD}$ and pays $c$, so it earns $(p_{CD} + p_{DC})b - c \le 2(b - c)$ per two rounds. ALLD earns $p_{DD}\,b \le b - c$. Necessity of each listed inequality follows from such a deviation; the paper's supplementary information proves that the listed cycles are the only binding ones, so the conditions are also sufficient.

## Sources

- N. E. Glynatsi, E. Akin, M. A. Nowak, C. Hilbe, "Conditional cooperation with longer memory", Proceedings of the National Academy of Sciences USA 121(50) (2024) e2420125121, Eqs. 1–2 and Figs. 2–3, <https://doi.org/10.1073/pnas.2420125121> (PMC11648855).
