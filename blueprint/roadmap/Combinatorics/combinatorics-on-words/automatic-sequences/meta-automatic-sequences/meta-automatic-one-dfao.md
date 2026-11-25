# An automaton for the meta-automatic sequence $\mathcal{M}_1$

The meta-automatic sequence
$\mathcal{M}_1$ is $4$-automatic. Moreover, let $\delta$ be the transition map on the states
$\{0, 1, 2, 3\}$ and the digits $\{0, 1, 2, 3\}$ given by $\delta(0, \cdot) = 0112$,
$\delta(1, \cdot) = 1230$, $\delta(2, \cdot) = 2301$ and $\delta(3, \cdot) = 3023$, where the
symbol at position $d$ (counted from $0$) of the word listed for $q$ is $\delta(q, d)$. For every
$n \in \mathbb{N}$, let $q_n$ be the state reached by starting in state $0$ and reading the
base-$4$ digits of $n$ with $\delta$, most significant digit first (no digits when $n = 0$).
Then, reading the values of $\mathcal{M}_1$ as $0$ and $1$, $\mathcal{M}_1(n) = q_n \bmod 2$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Theorem 13 (`jis-2026-26.4.1-thm-13`).
