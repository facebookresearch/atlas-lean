# Mansour–Safadi Theorem 3, class C2 (signed patterns 0̄0̄, 0̄0, 0̄1, 01)

A signed inversion
sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots,
k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$,
$10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$, and $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 0\bar 0, \bar 0 0, \bar 0 1, 01\}$ and
$B_2 = \{\bar 0\bar 0, \bar 0 1, 0\bar 0, 01\}$.
For every $n \ge 0$, $|\bar I_n(B_1)| = |\bar I_n(B_2)|$, and the coefficient of $x^n$ in
$F_{B_1}(x)$ equals the coefficient of $x^n$ in
$1 + 2\sum_{k=1}^{n} x^k \prod_{i=1}^{k} (1 - ix)^{-1}$.

Since the terms with $k > n$ contribute nothing to $x^n$, this says
$F_{B_1}(x) = 1 + 2\sum_{k \ge 1} x^k / \prod_{i=1}^{k} (1 - ix)$.

## Sources

- Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C2).
