# Minimal lattice walks with unit and diagonal steps

For all natural numbers $a$ and $b$,
the number of sequences of $\max(a, b)$ steps, each taken from $\{(1,0), (0,1), (1,1)\}$,
whose sum is $(a, b)$ equals $\binom{\max(a, b)}{\min(a, b)}$.

Every walk from the origin to $(a, b)$ with these steps has at least $\max(a, b)$ steps, since
each step raises each coordinate by at most $1$, and walks of exactly that length exist; so the
sequences counted are the minimal-length walks from the origin to $(a, b)$.

## Sources

- Jackson Evoniuk, Steven Klee, and Van Magnan, "Enumerating Minimal Length Lattice Paths," Journal of Integer Sequences 21 (2018), Article 18.3.6, Theorem (section Minimal walks for S = {(1,0),(0,1),(1,1)}, label sec2), lines 273–275, https://cs.uwaterloo.ca/journals/JIS/VOL21/Klee/klee2.tex
