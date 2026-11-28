# Discrete dynamics as labelled transition systems

Let $(X, U, f)$ be a deterministic discrete-time system with update map $f : X \times U \to X$, and let
$T_f$ be the labelled transition system with states $X$, labels $U$ and transitions
$x \xrightarrow{u} f(x,u)$. A labelled run of $T_f$ of length $n$ is a sequence
$x_0 \xrightarrow{u_1} x_1 \cdots \xrightarrow{u_n} x_n$ of transitions. Then:

1. for every initial state $x_0$ and input word $u_1 \cdots u_n$, the trajectory $x_k = f(x_{k-1}, u_k)$
   is the unique labelled run of $T_f$ from $x_0$ with label word $u_1 \cdots u_n$, so trajectories,
   indexed by initial state and input word, correspond one-to-one with labelled runs;
2. the set of states reachable from an initial set $I$ on some input word equals the set of states
   reachable from $I$ in $T_f$;
3. a set $S$ satisfies $f(S \times U) \subseteq S$ if and only if every transition of $T_f$ from a
   state of $S$ ends in $S$.

For a nondeterministic system with $\mathrm{Post} : X \times U \to 2^X$, the transitions are
$x \xrightarrow{u} x'$ for $x' \in \mathrm{Post}(x,u)$; labelled runs are then exactly the trajectories
with their inputs, and items 2 and 3 hold with $f(S \times U)$ replaced by
$\bigcup_{x \in S, u \in U} \mathrm{Post}(x,u)$. Labels are needed in item 1: the sequence of states
alone does not determine the input word when two inputs give the same successor.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and
links it under the dependency sections.

- Statement prerequisite: labelled transition systems and their labelled runs.

## Depends on

- [Discrete-time dynamical system (input-driven state-update map)](discrete-time-dynamical-system.md)
- [Reachable sets, forward invariants and safety for discrete dynamics](reachable-sets-forward-invariants-and-safety-for-discrete-dy.md)

## Sources

- E. A. Lee and S. A. Seshia, *Introduction to Embedded Systems: A Cyber-Physical Systems Approach*,
  second edition, Chapter 3: state machines and their update functions (Section 3.3.3), reachable
  states as the states reachable from the initial state on some input sequence (Section 3.4) and
  nondeterministic state machines (Section 3.5).
  <https://ptolemy.berkeley.edu/books/leeseshia/releases/LeeSeshia_DigitalV2_2.pdf>
