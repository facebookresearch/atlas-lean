# String-matching automaton

For a pattern $P$ of length $m$ over the alphabet
$\{0, \dots, A-1\}$, the string-matching automaton of $P$ is the deterministic finite automaton
with states $\{0, \dots, m\}$, input symbols $\{0, \dots, A-1\}$, start state $0$, accepting set
$\{m\}$, and transition from state $q$ on symbol $a$ given by the entry at index $qA + a$ of the
transition table of $P$.
