# I-Wilf-equivalence of 101 and 110 alongside 102, 120, 210

Write a length-3 pattern as the
word of its values, so $101$ is the pattern $(1, 0, 1)$, and for a set $S$ of patterns let
$|I_n(S)|$ be the number of inversion sequences of length $n$ that avoid every pattern in $S$.
Let $B_\tau = \{100, \tau, 102, 120, 210\}$ and $C_\tau = \{\tau, 102, 120, 201, 210\}$. Then for
every $n \ge 0$, $|I_n(B_{101})| = |I_n(B_{110})|$ and $|I_n(C_{101})| = |I_n(C_{110})|$.

The paper's Theorem 10 also claims $|I_n(A_{101})| = |I_n(A_{110})|$ for all $n$, where
$A_\tau = \{100, \tau, 102, 120, 201\}$; that claim is false, since for $n = 6$ the two counts
are $206$ and $205$.

## Sources

- Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024), Article A76, Theorem 10.
