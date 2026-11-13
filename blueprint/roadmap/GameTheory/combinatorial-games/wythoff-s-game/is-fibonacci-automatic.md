# Fibonacci-automatic sequences

A sequence $u : \mathbb{N} \to \mathbb{N}$ is
Fibonacci-automatic if there are a finite set $Q$ of states, a transition function
$\delta : Q \times \{0, 1\} \to Q$, an initial state $q_0 \in Q$ and an output map
$\tau : Q \to \mathbb{N}$ such that for every $n$, $u(n) = \tau(q)$, where $q$ is the state
reached from $q_0$ by reading the digits of the greedy Fibonacci representation
$\mathrm{rep}_F(n)$ with $\delta$, most significant digit first.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Section 2 (Fibonacci-automatic sequences, DFAO fed with `rep_F(n)`).
