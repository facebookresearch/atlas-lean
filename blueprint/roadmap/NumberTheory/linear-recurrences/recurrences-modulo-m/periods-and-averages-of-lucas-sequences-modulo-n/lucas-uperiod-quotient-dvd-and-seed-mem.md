# Period quotients and seeds of $S(U)$

Let $U = U(P, Q)$ be a nondegenerate Lucas
sequence with $Q = -1$, or $Q = 1$, or $Q$ odd and $P = -Q - 1$. Write $\pi_U(m)$ and
$\rho_U(m)$ for the least period and the least restricted period of $U$ modulo $m$, and $S(U)$
for the set of positive integers $n$ coprime to $Q$ with $\pi_U(n) \mid n$. For every prime
$p \nmid Q$, $\rho_U(p)$ divides $\pi_U(p)$, and the quotient $\pi_U(p) / \rho_U(p)$ divides $4$
if $Q = -1$ and divides $2$ if $Q \ne -1$. Moreover, each of the following numbers $s_0$ lies in
$S(U)$: $s_0 = 1$; $s_0 = 6$ if $P \equiv 3 \pmod 6$ and $Q = -1$, or if $P \equiv \pm 1 \pmod 6$
and $Q = 1$; $s_0 = 24$ if $P \equiv \pm 1 \pmod 6$ and $Q = -1$; $s_0 = 12$ if
$P \equiv 3 \pmod 6$ and $Q = 1$; $s_0 = 2$ if $Q$ is odd and $P = -Q - 1$.

In the paper's notation $W(n + 2) = a W(n + 1) + b W(n)$ one has $a = P$ and $b = -Q$. The
paper also characterizes $S(U)$ by chains $n_0 = s_0$, $n_i = n_{i-1} s_i 2^{\varepsilon(s_i)}$
with primes $s_i \mid D U_{n_{i-1}}$, where $D = P^2 - 4Q$ and
$\varepsilon(s_i) = \max(\nu_2(\pi_U(s_i)) - \nu_2(n_{i-1}), 0)$; that characterization is
false as printed in both directions and is omitted. For $(P, Q) = (-10, 1)$ only $s_0 = 1$ is
admissible and $\pi_U(2) = 2$, so $2 \in S(U)$, but the only chain that could end at $2$ has
$s_1 = 2$, and then $\varepsilon(2) = \nu_2(\pi_U(2)) = 1$ gives $n_1 = 4$. For
$(P, Q) = (-11, 1)$, where $D = 117$, the chain $s_0 = 1$, $s_1 = 13$,
$s_2 = 53 \mid U_{13} = 2862615066961$ gives $\varepsilon(53) = \nu_2(26) = 1$ and
$n_2 = 1378$, while $\pi_U(1378) = 78 \nmid 1378$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 4.3 (`integers-2024-A36-thm-4-3`).
