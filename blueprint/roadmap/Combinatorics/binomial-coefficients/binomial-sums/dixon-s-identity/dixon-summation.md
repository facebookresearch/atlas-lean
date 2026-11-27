# Dixon's summation theorem

For an integer $m$ write $m!$ for the extended factorial
and $\frac{1}{m!}$ for the inverse factorial; both are $0$ when $m < 0$. For all integers
$a_1, a_2, a_3$, the Dixon sum $\Upsilon_3(a_1, a_2, a_3)$ equals

$$
(2a_1)!\,(2a_2)!\,(2a_3)!\,(a_1 + a_2 + a_3)! \cdot
\frac{1}{(a_1 + a_2)!} \cdot \frac{1}{(a_1 + a_3)!} \cdot \frac{1}{(a_2 + a_3)!} \cdot
\frac{1}{a_1!} \cdot \frac{1}{a_2!} \cdot \frac{1}{a_3!}.
$$

Proof: a Wilf–Zeilberger pair. For $a = a_1 \ge 0$ and $b = a_2 \ge 0$ the normalized summand
in $c = a_3$ has the certificate ratio
$R(c, k) = -\frac{(a + k)(b + k)}{2(c - k + 1)(a + b + c + 1)}$; induction on $c$ telescopes
over the fixed window $[-a, a]$. Negative arguments make both sides zero.

## Sources

- Abdelmalek Abdesselam, *An algebraic independence result related to a conjecture of Dixmier on binary form invariants*, Res. Math. Sci. 6 (2019), DOI 10.1007/s40687-019-0189-x; arXiv:1903.11147v2, Proposition 5 (Dixon), <https://arxiv.org/abs/1903.11147v2>.
