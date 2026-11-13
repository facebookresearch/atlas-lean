# Seed automaton after reading the digit 1

Let $\eta$ be a letter map, let $a$ and $b$ be
letters, and let $\mathcal{A}_{\eta,s}$ be the seed automaton for the seed $s = b|a$. For every
digit word $w$, the value of $\mathcal{A}_{\eta,s}$ on the word $1w$ (the digit $1$ followed by
$w$) equals the value $\mathcal{A}_{\eta,b}(w)$ of the substitution automaton started at $b$ on
$w$: either both are undefined, or both are the same state.

## Sources

- Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 6, Equation (automata relations).
