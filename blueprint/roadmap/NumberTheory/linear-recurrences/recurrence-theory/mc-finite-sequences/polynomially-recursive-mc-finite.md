# Polynomially recursive integer sequences are MC-finite

Call an integer sequence $s$
MC-finite if for every natural number $m > 0$ there are natural numbers $p > 0$ and $q > 0$ and
integers $c_0, \dots, c_{p-1}$ such that $m$ divides $s(n + p) - \sum_{i=0}^{p-1} c_i\, s(n + i)$
for all $n \ge q$. Every integer sequence $s$ has the following two properties.

(1) If there are $k \ge 0$, integer sequences $u_0, \dots, u_k$ with $s = u_0$, and polynomials
$P_0, \dots, P_k$ with integer coefficients in $k + 2$ variables such that
$u_i(n+1) = P_i(u_0(n), \dots, u_k(n), n)$ for all $i \le k$ and all $n \ge 0$, then $s$ is
MC-finite.

(2) Holonomic case: if there are $k > 0$ and polynomials $P_1, \dots, P_k$ with integer
coefficients such that $P_1 \ne 0$, $P_k \ne 0$ and $s(n) = \sum_{i=1}^{k} P_i(n)\, s(n - i)$ for
all $n \ge k$, then $s$ is MC-finite.

## Sources

- Yuval Filmus, Eldar Fischer, and Johann A. Makowsky, with Vsevolod Rakita, "MC-Finiteness of Restricted Set Partition Functions," Journal of Integer Sequences 26 (2023), Article 23.7.4, Theorem, lines 422–427, with the MC-finite definition at lines 281–286 and the holonomic/PRS definitions at lines 387–412, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>. It follows from `isMCFinite_of_mvPolynomial_recursion` and `IsPRecursiveSequence.isMCFinite`; in the holonomic premise the conditions `0 < k`, `P 1 ≠ 0` and `P k ≠ 0` are unused and keep the source's shape.
