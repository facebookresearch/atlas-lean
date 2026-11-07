# Alternating sum- and difference-dominated sets from Nathanson's construction

For a set
$S$ of integers write $S + S = \{s + s' : s, s' \in S\}$, $S - S = \{s - s' : s, s' \in S\}$,
$c + S = \{c + s : s \in S\}$ and $c - S = \{c - s : s \in S\}$. Let $m$, $d$, $k$ be integers with
$m \ge 4$, $m \equiv 0 \pmod 4$ and $4d = m$ or $4d = 3m$, and suppose $k \ge 3$ if $2d < m$ and
$k \ge 4$ if $2d > m$. Let $B = \{0, 1, \dots, m - 1\} \setminus \{d\}$,
$L = \{jm - d : 1 \le j \le k\}$ and $A^* = B \cup L \cup \{(k + 1)m - 2d - b : b \in B\}$. Let
$A_1, A_2, A_3, \dots$ be finite sets of integers with $A_1 = A^* \cup \{m, -d, (k + 1)m - d\}$
and, for every $r \ge 1$, $A_{2r} = A_{2r-1} \cup \{(k + r + 1)m - d\}$ and
$A_{2r+1} = A_{2r-1} \cup \{-rm - d, (k + r + 1)m - d\}$. Then $|A_1 - A_1| < |A_1 + A_1|$, and
for every $r \ge 1$, writing $A'_{2r-1} = A_{2r-1} \setminus \{m\}$: we have
$|A_{2r} + A_{2r}| < |A_{2r} - A_{2r}|$ and $|A_{2r+1} - A_{2r+1}| < |A_{2r+1} + A_{2r+1}|$;
$A_{2r-1} \subsetneq A_{2r} \subsetneq A_{2r+1}$; $m + A'_{2r-1} \subseteq A'_{2r-1} + A'_{2r-1}$
and $m - A'_{2r-1} \subseteq A'_{2r-1} - A'_{2r-1}$;
$|A_{2r-1} + A_{2r-1}| = |A_{2r-1} - A_{2r-1}| + 1$; and
$|A_{2r} + A_{2r}| \le |A_{2r} - A_{2r}| - m + 3$.

## Sources

- Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 3 (`integers-2026-A88-thm-3`).
