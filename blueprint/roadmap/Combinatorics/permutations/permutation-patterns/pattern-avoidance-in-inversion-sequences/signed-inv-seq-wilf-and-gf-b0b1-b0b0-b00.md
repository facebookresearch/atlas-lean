# Mansour–Safadi Theorem 3, class C4 (signed patterns 0̄1̄, 0̄0̄, 0̄0, 01̄)

A signed
inversion sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1,
\dots, k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$,
$01$, $10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$. Let $B_1 = \{\bar 0\bar 1, \bar 0\bar 0, \bar 0 0, 0\bar 1\}$,
$B_2 = \{\bar 0\bar 1, \bar 0\bar 0, 0\bar 1, 0\bar 0\}$,
$B_3 = \{\bar 0\bar 1, \bar 0 0, 0\bar 1, 0\bar 0\}$ and
$B_4 = \{\bar 0 0, \bar 0 1, 0\bar 1, 0\bar 0\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)| = |\bar I_n(B_4)|$ for every $n \ge 0$, and
$|\bar I_n(B_1)| = 2\,n!$ for every $n \ge 1$.

Together with $|\bar I_0(B)| = 1$, which holds for every $B$, this says that
$\sum_{n \ge 0} |\bar I_n(B_1)|\,x^n = 1 + 2\sum_{k \ge 1} k!\,x^k$.

## Sources

- Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C4) (`integers-2026-A74-thm-3`).
