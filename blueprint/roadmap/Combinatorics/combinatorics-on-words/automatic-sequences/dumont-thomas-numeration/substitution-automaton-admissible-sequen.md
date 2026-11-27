# The automaton reads off the letters of an admissible sequence

Let $\eta$ be a
substitution, let $x$ be a letter, let $k \ge 1$, and let $(m_i, a_i)_{i = 0, \dots, k-1}$ be an
$x$-admissible sequence. Then for every $i < k$, the substitution automaton started at $x$ ends in
the state $a_i$ after reading the digit word $|m_{k-1}|\,|m_{k-2}| \cdots |m_i|$, whose digits are
the lengths of $m_{k-1}, \dots, m_i$ in this order.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.6.
