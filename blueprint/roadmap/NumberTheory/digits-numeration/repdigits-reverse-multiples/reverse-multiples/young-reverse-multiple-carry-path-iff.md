# Carry equations for reverse multiples

Let $g, k, n$ be natural numbers with
$2 \le k < g$ and $n \ge 1$, and let $a_0, \dots, a_{n-1}$ be natural numbers with $a_i < g$ for
every $i$, $a_{n-1} \ne 0$ and $a_0 \ne 0$. Then $k \sum_{i\lt n} a_i g^i = \sum_{i\lt n} a_{n-1-i} g^i$,
that is, $k$ times the number with base-$g$ digits $a_{n-1}, \dots, a_0$ (most significant first)
equals the number with these digits reversed, if and only if there is a unique sequence of natural
numbers $r_0, \dots, r_n$ with $r_0 = 0$, $r_n = 0$ and, for every $i < n$, $r_{i+1} < k$ and
$k a_i + r_i = a_{n-1-i} + r_{i+1} g$.

The carry $r_{i+1}$ here is the source's $r_i$. The conditions $a_0 \ne 0$ and $a_{n-1} \ne 0$ are
not needed for the equivalence; see the general form.

## Sources

- L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer Sequences 18 (2015), Article 15.9.7, Section 2.1 (the column equations for $kN = \mathrm{Reverse}_g(N)$ and Young's bound $r_i \le k - 1$), <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>.
