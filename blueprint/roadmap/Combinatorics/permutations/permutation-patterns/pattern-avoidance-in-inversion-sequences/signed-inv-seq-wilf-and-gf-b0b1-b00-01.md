# Mansour–Safadi Lemma 1 (signed patterns 0̄1̄, 0̄0, 01)

A signed inversion sequence of
length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots, k - 1,
\overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$, $10$,
each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as $|\tau_1|$,
$|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write $\bar I_n(B)$ for the
set of signed inversion sequences of length $n$ that avoid every pattern in $B$, and
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 0\bar 1, \bar 0 0, 01\}$ and $B_2 = \{\bar 0\bar 1, \bar 0 1, 01\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)|$ for every $n \ge 0$, and $(1 - 3x + x^2)\,F_{B_1}(x) = 1 - x$,
that is, $F_{B_1}(x) = (1 - x)/(1 - 3x + x^2)$.

## Sources

- Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 1.
