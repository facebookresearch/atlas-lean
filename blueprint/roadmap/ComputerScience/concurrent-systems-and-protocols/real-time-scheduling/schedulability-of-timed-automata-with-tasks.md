# Schedulability of timed automata with tasks is undecidable

For timed automata that release real-time tasks with interval execution times, where tasks reset a clock on completion and a fixed-priority scheduler may preempt them, it is undecidable whether every task always meets its deadline.

**Setting (Krčál and Yi).** A *timed automaton extended with tasks* over a finite set $C$ of clocks and a finite set $P$ of task types is a timed automaton $\langle N, l_0, E, I \rangle$ (locations $N$, initial location $l_0$, edges labeled by clock guards and clock resets, location invariants of the form $a < n$ or $a \le n$) together with a partial map $M : N \to P$ and a distinguished clock $\mathit{check} \in C$. Each task type $P$ has a best-case execution time $b(P)$, a worst-case execution time $w(P)$ and a relative deadline $d(P)$. Entering a location $m$ with $M(m)$ defined releases an instance of $M(m)$ into a task queue; time elapsing executes the first task of the queue, which may finish once it has run at least $b(P)$ and must finish once it has run $w(P)$, and its completion resets $\mathit{check}$. A *scheduling strategy* reorders the queue by task type; it is *preemptive* when it may change the running task. An automaton with an initial state is *schedulable* with a strategy when no reachable state has a released task that has not finished by its deadline.

**Theorem (Krčál and Yi).** It is undecidable whether a given timed automaton extended with tasks is schedulable with the fixed-priority scheduling strategy.

The source notes that the proof also applies, without change, to earliest-deadline-first scheduling, and that schedulability becomes decidable when any one of the three features is removed: with non-preemptive scheduling, when tasks do not reset clocks, or when every task has $b(P) = w(P)$.

## Depends on

- [Timed Büchi automata and timed regular languages](../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-buchi-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof encodes the halting problem of a two-counter machine, following the wrapping technique of Henzinger, Kopke, Puri and Varaiya for hybrid automata. The automaton is $4$-wrapping: a system clock is reset each time it reaches $4$, and a counter value $v$ is stored as the value $2^{1 - v}$ of a clock at the moments when the system clock is $0$. Incrementing and decrementing halve and double that value, and the zero test checks whether it equals $2$. Doubling uses two tasks: a long task with execution time exactly $8$ and a higher-priority short task with execution time in $[0, 1]$; the response time of the long task, recorded by resetting a clock on its completion, grows by the running times of the two short instances that preempt it, so its completion time measures a sum of execution times. The machine halts exactly when the automaton reaches a state from which a deadline is missed.

## Sources

- Pavel Krčál and Wang Yi, *Decidable and Undecidable Problems in Schedulability Analysis Using Timed Automata*, Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2004), Lecture Notes in Computer Science 2988, Springer, 2004, pp. 236–250, https://doi.org/10.1007/978-3-540-24730-2_20; Definitions 1–4 and Theorems 1–4, read in the open-access copy at https://link.springer.com/content/pdf/10.1007/978-3-540-24730-2_20.pdf.
