# Size-degree trade-off for Sums-of-Squares and Positivstellensatz proofs

A Positivstellensatz refutation of monomial size $s$ and product-width $w$ over $n$ pairs of twin variables can be converted into one of the same product-width and degree at most $4\sqrt{2(n+1)\log s} + kw + 4$, so linear degree lower bounds yield exponential monomial-size lower bounds for Sums-of-Squares.

Work over $\mathbb{R}[x]$ with variables $x_1, \dots, x_n$ and twins $\bar{x}_1, \dots, \bar{x}_n$, and let $B_n$ be the Boolean axioms with twins, generating the ideal $I_n$. Let $Q = \{q_1, \dots, q_\ell, p_1, \dots, p_m\}$ be an indexed set of polynomials read as $q_j \ge 0$ and $p_j = 0$. A **Positivstellensatz (PS) proof** of $p \ge 0$ from $Q$ is an identity

$$
p = s_{\emptyset} + \sum_{J \in \mathscr{J}} s_J \prod_{j \in J} q_j + \sum_{j \in [m]} t_j p_j + \sum_{q \in B_n} u_q q ,
$$

with $\mathscr{J}$ a collection of nonempty subsets of $[\ell]$, each $s_J = \sum_i r_{i,J}^2$ a sum of squares and $t_j, u_q$ arbitrary. Its degree is at most $d$ if $\deg p$, $\deg s_\emptyset$, $\deg s_J + \sum_{j \in J} \deg q_j$ and $\deg t_j + \deg p_j$ are all at most $d$; its monomial size is $\sum_{i,J} \mathrm{size}(r_{i,J}) + \sum_j \mathrm{size}(t_j)$; its product-width is $\max_{J} |J|$. A refutation proves $-1 \ge 0$. With at most one inequality ($\ell \le 1$), PS is literally Sums-of-Squares (SOS).

**Theorem.** For all natural numbers $n$ and $k$, every indexed set $Q$ of polynomials of degree at most $k$ in $n$ pairs of twin variables, and all positive integers $s$ and $w$: if $Q$ has a PS refutation of product-width at most $w$ and monomial size at most $s$, then $Q$ has a PS refutation of product-width at most $w$ and degree at most

$$
4\sqrt{2(n+1)\log(s)} + kw + 4 .
$$

**Corollary.** If $d$ is the minimum degree and $s$ the minimum monomial size of PS refutations of $Q$ of product-width at most $w$, and $d \ge kw + 4$, then $s \ge \exp((d - kw - 4)^2/(32(n+1)))$.

## Proof sketch

The proof follows the standard structure of degree-reduction lemmas for other proof systems, but because PS proofs are static the unrestricting lemmas are harder; it is handled by a tight duality theorem for degree-bounded proofs with respect to cut-off functions, built on vector spaces with an order unit. Applications: Tseitin formulas on constant-degree expanders need SOS monomial size $2^{\epsilon n}$, the knapsack equations $2x_1 + \dots + 2x_n = k$ for odd $k$ need size $2^{\epsilon k^2/n}$, and random 3-XOR and 3-SAT instances inherit exponential bounds from Grigoriev and Schoenebeck's linear degree lower bounds. For polynomial calculus the analogous statement is the Impagliazzo-Pudlák-Sgall relation. For Sherali-Adams a bound $O(\sqrt{n \log s} + \deg(\mathcal{P}))$ was claimed earlier, but Atserias and Hakoniemi note that the claim was made without proof and that the published sketch cannot be completed, so the [Sherali-Adams proof system](sherali-adams-proof-system.md) page does not assert it.

## Depends on

- [Sums-of-Squares proof system](../sums-of-squares-proof-system.md)

## Proof depends on

None.

## Sources

- Albert Atserias, Tuomas Hakoniemi, "Size-degree trade-offs for sums-of-squares and Positivstellensatz proofs", *34th Computational Complexity Conference (CCC 2019)*, LIPIcs 137, 2019, https://doi.org/10.4230/LIPIcs.CCC.2019.24; numbering of arXiv:1811.01351v2 (Theorem 1, Corollaries 1 to 4, Theorem 2, Sections 2 and 5, footnote 1).
