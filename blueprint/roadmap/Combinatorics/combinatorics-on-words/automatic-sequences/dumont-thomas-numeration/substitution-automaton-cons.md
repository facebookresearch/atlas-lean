# Reading a nonempty digit word

Let $\eta$ be a letter map, $b$ a letter, $i$ a digit and
$w$ a digit word. If $i < |\eta(b)|$, then the value of the substitution automaton started at $b$
on the word $iw$ (the digit $i$ followed by $w$) equals its value started at $\eta(b)_i$ on $w$,
where $\eta(b)_i$ is the letter of $\eta(b)$ at position $i$, counting from $0$. If
$i \ge |\eta(b)|$, the run on $iw$ is undefined.

## Sources

- Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 2.
