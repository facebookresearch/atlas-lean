# A dwell-time bound rules out Zeno executions

An infinite execution of a hybrid automaton with hybrid time set $\tau = (I_i)_{i \ge 0}$, $I_i = [\tau_i, \tau'_i]$, is **Zeno** if its total elapsed time is finite, $\sum_{i \ge 0} (\tau'_i - \tau_i) < \infty$; it is **time-divergent** if $\tau'_i \to \infty$. For instance a bouncing ball whose velocity is multiplied by a coefficient $c \in (0, 1)$ at each impact has infinitely many impacts in finite time.

Suppose that an infinite execution has a **dwell time** $\delta > 0$: every interval between two discrete transitions has length at least $\delta$, that is, $\tau'_i - \tau_i \ge \delta$ for all $i \ge 1$. Then:

1. the execution is time-divergent, with $\tau'_k - \tau_0 \ge k\delta$ for all $k \ge 1$; in particular it is not Zeno;
2. for every $T \ge \tau_0$, the execution makes at most $\lfloor (T - \tau_0)/\delta \rfloor + 1$ discrete transitions up to time $T$.

Without a uniform $\delta$ the conclusion fails: positive lengths $\tau'_i - \tau_i = 2^{-i}$ give a Zeno time set.

**Proof.** By the defining property $\tau'_i = \tau_{i+1}$ of hybrid time sets, $\tau'_k - \tau_0 = \sum_{i=0}^k (\tau'_i - \tau_i) \ge k\delta$, which tends to infinity. The discrete transitions happen at the times $\tau'_i$; those with $\tau'_k \le T$ satisfy $k\delta \le T - \tau_0$, which gives part 2. The counterexample sums to $2$.

## Depends on

- [Executions of a hybrid automaton](executions-of-a-hybrid-automaton.md): hybrid time sets and executions

## Background

- [Zeno executions and finite-jump hypotheses](../remaining-clauses-of-zeno-executions-and-finite-jump-hypothe.md): the remaining clauses on Zeno executions, apart from this positive-dwell case

## Sources

- J. Lygeros, *Lecture Notes on Hybrid Systems*, ENSIETA, 2004, <https://people.eecs.berkeley.edu/~sastry/ee291e/lygeros.pdf>, Definition 3.5 (finite, infinite and Zeno executions, with Zeno meaning infinite with $\sum_i (\tau'_i - \tau_i) < \infty$, p. 26) the bouncing ball with restitution $x_2 := -c x_2$ (Section 3.1.1, p. 17), and Section 4.4 (Zeno executions take infinitely many discrete transitions in finite time, p. 34). The dwell-time bound is derived on the page.
