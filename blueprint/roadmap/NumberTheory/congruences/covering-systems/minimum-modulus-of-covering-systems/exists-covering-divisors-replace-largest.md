# Replacing the largest prime factor of the modulus set

Let $m, L \in \mathbb{N}$, let
$p \ge m$ be a prime with $p \nmid L$, let $q > p$ be the largest prime dividing $L$, and write
$\nu_q(L)$ for the exponent of $q$ in $L$. Suppose there are residues $r_d \in \mathbb{Z}$, one
for each divisor $d \ge m$ of $L$, such that every integer $x$ satisfies $x \equiv r_d \pmod d$
for some such $d$. Then the same holds with $L$ replaced by $p^{\nu_q(L)} L / q^{\nu_q(L)}$:
there are residues $s_d \in \mathbb{Z}$, one for each divisor $d \ge m$ of
$p^{\nu_q(L)} L / q^{\nu_q(L)}$, such that every integer $x$ satisfies $x \equiv s_d \pmod d$
for some such $d$.

## Sources

- Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*, INTEGERS 26 (2026), Article A38, Lemma 6 (`integers-2026-A38-lem-6`).
