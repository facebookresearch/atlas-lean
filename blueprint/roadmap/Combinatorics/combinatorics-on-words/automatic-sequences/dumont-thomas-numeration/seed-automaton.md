# Seed automaton

Let $\eta$ be a letter map and let $s = b|a$ be the seed formed by the
letters $b$ and $a$. The automaton $\mathcal{A}_{\eta,s}$ has a new initial state, which is not
final, with a transition labelled $0$ to $a$ and a transition labelled $1$ to $b$; from a letter
it runs like the substitution automaton $\mathcal{A}_{\eta,\cdot}$. So its value on a digit word
is: undefined on the empty word; $\mathcal{A}_{\eta,a}(w)$ on $0w$, the state reached from $a$ by
reading $w$ (undefined when that run is undefined); $\mathcal{A}_{\eta,b}(w)$ on $1w$, likewise;
and undefined on every word whose first digit is at least $2$.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 6 (the automaton `𝒜_{η,s}`).
