# Upper bound on the expected time to the most recent common ancestor of the seed-bank coalescent

Let $c, K \in (0, \infty)$ and let $T_{\mathrm{MRCA}}[n]$ be the time to the most recent common ancestor of
$n$ initially active lineages in the [seed-bank coalescent](seed-bank-coalescent-active-dormant-lineages.md) with seed-bank intensity $c$ and
relative seed-bank size $1/K$. Then

$$\limsup_{n \to \infty} \frac{\mathbb E\, T_{\mathrm{MRCA}}[n]}{\log \log n} < \infty .$$

## Depends on

- [Seed-bank coalescent: active/dormant lineages](seed-bank-coalescent-active-dormant-lineages.md)

## Expansion

A sound expansion follows the source proof. Let $\rho_n$ be the stopping time at which the lines that
have not visited the seed bank so far have coalesced into one; comparison with Kingman's coalescent
gives $\mathbb E \rho_n \le 2$. By the strong Markov property and monotone comparison,

$$\mathbb E\, T_{\mathrm{MRCA}}[(n, 0)] \le 2 + \mathbb E\, T_{\mathrm{MRCA}}\bigl[(0,\, N_{\rho_n} + M_{\rho_n})\bigr],$$

that is, the remaining mixed population is dominated by one in which every block starts dormant. The
total $N_{\rho_n} + M_{\rho_n}$ is at most $A_n + 1$ with $A_n$ of order $2c \log n$, and an auxiliary
process in which coalescence is suppressed while fewer than $\sqrt{n + m}$ of the $n + m$ blocks are active,
coupled with the seed-bank coalescent so that its time to one block is at least as large, has expected
time to one block at most $C \log m$ from $m$ dormant blocks. The source gives the computations for
this auxiliary bound only for $c = K = 1$ and leaves the general case to the reader.

## Sources

- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 4, Definition 4.9, Lemmas 4.10 and 4.11, equations (4.25)–(4.27) and Proposition 4.12 (the upper half of Theorem 4.6).
