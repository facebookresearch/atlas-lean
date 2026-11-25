# Zeno executions and finite-jump hypotheses

An execution of a hybrid automaton is Zeno if it has infinitely many discrete transitions in finite time.
The positive-dwell case (with a positive minimum dwell time, the elapsed time tends to infinity and only finitely
many events occur in any bounded time interval) is a separate result and is not part of this node. This node
collects the remaining clauses.

## Expansion

A sound expansion has separate pages for:

1. the definition of a Zeno execution for the selected hybrid-automaton model;
2. a finite-horizon jump-count bound under a dwell-time hypothesis $\tau_D > 0$, with the counting
   convention fixed: if every two consecutive jumps are separated by at least $\tau_D$, then for every
   $T \ge 0$ the number of jumps in $[0,T]$ is at most $\lfloor T/\tau_D \rfloor + 1$ when a jump at time $0$ is counted;
3. the statement form for safety theorems over a horizon $[0,T]$: they quantify over executions with
   finitely many jumps on $[0,T]$, or assume a dwell-time hypothesis.

## Depends on

- [Hybrid automata and their executions](hybrid-automata-and-their-executions.md)

## Sources

- J. Zhang, K. H. Johansson, J. Lygeros and S. Sastry, *Zeno hybrid systems*, International Journal of
  Robust and Nonlinear Control 11 (2001), abstract and introduction: Zeno executions as executions with
  infinitely many discrete transitions in finite time.
  <https://people.eecs.berkeley.edu/~sastry/pubs/OldSastryALL/ZhangZenoHybridSystems2001.pdf>
