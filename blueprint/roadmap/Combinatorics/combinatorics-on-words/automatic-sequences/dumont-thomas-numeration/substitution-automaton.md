# Substitution automaton

Let $\eta$ map each letter of an alphabet $A$ to a finite word
over $A$. The substitution automaton $\mathcal{A}_{\eta,\cdot}$ of $\eta$ is the deterministic
automaton with output whose states are the letters of $A$ (the alphabet need not be finite):
reading a digit $i \in \mathbb{N}$ in the state $b$ moves to the letter $\eta(b)_i$ of $\eta(b)$
at position $i$, counting from $0$, and is undefined when $i \ge |\eta(b)|$. For a letter $b$
and a finite word $w$ of digits, the automaton started at $b$ returns the state reached after
reading $w$ from left to right (on the empty word this is $b$ itself), or no state when some step
of the run is undefined.

Every state is final, so a digit word is accepted from a letter $b$ exactly when the run from $b$
is defined. When $A$ is finite, digits outside the paper's alphabet
$\{0, \dots, \max_c |\eta(c)| - 1\}$ are never readable, so the accepted language is unchanged.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (the DFAO `𝒜_{η,a}`).
