# Reordering makes OBDD proofs with weakening strictly stronger

There are polynomial-size CNF formulas with polynomial-size refutations in OBDD proofs using join, weakening and reordering, while every refutation using only join and weakening in a single variable order has size exponential in a power of the number of variables.

**Theorem.** There are a family of CNF formulas $\varphi_n$ and a constant $c > 0$ such that:

1. $\varphi_n$ has size $\mathrm{poly}(n)$;
2. there is an $\mathrm{OBDD}(\wedge, \mathrm{weakening}, \mathrm{reordering})$ proof of $\varphi_n$ of size $\mathrm{poly}(n)$;
3. any $\mathrm{OBDD}(\wedge, \mathrm{weakening})$ proof of $\varphi_n$ has size $\Omega(2^{n^c})$.

Hence $\mathrm{OBDD}(\wedge, \mathrm{weakening})$ does not polynomially simulate $\mathrm{OBDD}(\wedge, \mathrm{weakening}, \mathrm{reordering})$. The formulas are $\varphi_n = T(\psi_n)$ for $\psi_n = \text{Clique-Coloring}_{n,\sqrt{n}}$, the CNF stating that a graph on $n$ vertices (edge variables $p_{i,j}$) has an $m$-clique (variables $q_{k,i}$) and an $(m-1)$-coloring (variables $r_{i,l}$), here with $m = \sqrt{n}$ and with the extra clauses $\neg q_{k,i} \vee \neg q_{k,j}$.

## Expansion

Three ingredients combine. (1) Clique-Coloring is order-sensitive: there is an order $\pi$ under which every $\pi$-$\mathrm{OBDD}(\wedge, \mathrm{weakening})$ proof of $\text{Clique-Coloring}_{n,\sqrt{n}}$ has size at least $2^{n^{1/5}}$ (Atserias-Kolaitis-Vardi and Krajíček, via monotone feasible interpolation from the low communication complexity of OBDDs across an order cut), yet there is another order with polynomial-size $\mathrm{OBDD}(\wedge, \mathrm{weakening})$ proofs (Theorem 8, simulating the short degree-4 Lovász-Schrijver proofs of Grigoriev et al.). (2) Segerlind's transformation $T(\varphi) = \mathrm{perm}(\varphi^{\vee m})$ replaces each variable by an OR of $m = O(n^3)$ fresh variables and guards copies of the formula, one per affine permutation $x \mapsto ax + b$ over $\mathrm{GF}(2^{\lceil \log n \rceil})$ with $a \neq 0$, by selector variables $z$; restricting the selectors and all but one variable per OR block turns a proof of $T(\varphi)$ in any order into a proof of $\varphi$ in any prescribed order of no larger size (Lemma 1), so $T(\psi_n)$ is hard in every order. (3) Conversely, a proof of $\varphi$ in one good order lifts to an $\mathrm{OBDD}(\wedge, \mathrm{weakening}, \mathrm{reordering})$ proof of $\mathrm{perm}(\varphi)$ of size $t(n)\,\mathrm{poly}(n)$ by running one copy per permutation in a matching order and reordering before combining (Lemma 2), and orification preserves short proofs when every clause has $O(1)$ negated literals (Theorem 5), which holds for Clique-Coloring. The same paper shows the separation of $\mathrm{OBDD}(\wedge, \mathrm{weakening})$ from $\mathrm{OBDD}(\wedge, \mathrm{reordering})$ is only quasipolynomial (Theorem 24).

## Depends on

- [OBDD-based proof systems with join, weakening and reordering](obdd-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Dmitry Itsykson, Alexander Knop, Dmitry Sokolov, "Reordering Rule Makes OBDD Proof Systems Stronger", *33rd Computational Complexity Conference (CCC 2018)*, LIPIcs, 2018, doi:10.4230/LIPIcs.CCC.2018.16 (Theorem 10; Definition 7, Theorems 8 and 9, Lemmas 1 and 2, Theorem 5, Section 3).
