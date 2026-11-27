# IPS simulates Frege, Extended Frege and bounded-depth Frege with modular gates

Linear IPS over formulas polynomially simulates Frege and linear IPS over circuits simulates Extended Frege; over $\mathbb{F}_p$, IPS of depth $d+2$ p-simulates depth-$d$ Frege over unbounded fan-in $\lor$, $\neg$ and $\mathrm{MOD}_p$ connectives, so for constant $d$ it simulates $\mathrm{AC}^0_d[p]$-Frege.

**Frege and Extended Frege.** Let $\varphi = C_1 \wedge \dots \wedge C_m$ be an unsatisfiable CNF on $n$ variables with polynomial encoding $f_1, \dots, f_m$. If there is a size-$s$ Frege (resp. Extended Frege) proof that $\{f_j\}_j, \{x_i^2 - x_i\}_i$ is unsatisfiable, then there is a formula-$\mathrm{IPS}_{\mathrm{LIN}}$ (resp. circuit-$\mathrm{IPS}_{\mathrm{LIN}}$) refutation of size $\mathrm{poly}(n, m, s)$, checkable in randomized $\mathrm{poly}(n, m, s)$ time. The circuits obtained from Extended Frege have polynomial size but no degree guarantee and may compute polynomials of exponential degree, while the formulas obtained from Frege have polynomially bounded degree.

**Depth-preserving simulation.** For any $d = d(n)$, depth-$(d+2)$ $\mathrm{IPS}_{\mathbb{F}_p}$ p-simulates depth-$d$ Frege proofs with unbounded fan-in $\lor$, $\neg$ and $\mathrm{MOD}_p$ connectives.

## Proof sketch

The first simulation goes back to Pitassi's 1996 algebraic system, which is p-equivalent to Hilbert-like IPS; her proof that this system simulates Polynomial Calculus and Frege extends to Extended Frege. That argument does not preserve depth, so the depth-preserving result is proved separately. The proof is given for $p = 2$, the other primes being analogous, and works with a sequent-calculus formalization of $\mathrm{AC}^0[2]$-Frege (a small modification of the one of Maciel and Pitassi) whose lines are cedents $\Gamma \rightarrow \Delta$ of $\{\lor, \neg, \mathrm{MOD}_p\}$-formulas of depth at most $d$, with axioms $A \rightarrow A$, $\lor() \rightarrow$ and $\rightarrow \neg \oplus()$; each line is translated into a polynomial and each rule into a bounded-depth circuit step, and nothing in the argument uses that $d$ is constant.

## Depends on

- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)
- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

- [Polynomial calculus line count is p-equivalent to Hilbert-like determinantal IPS](pc-line-count-equivalent-to-hilbert-like-determinantal-ips.md)

## Sources

- Joshua A. Grochow, Toniann Pitassi, "Circuit complexity, proof complexity, and polynomial identity testing: the Ideal Proof System", *Journal of the ACM* 65(6), 2018, https://doi.org/10.1145/3230742; numbering of arXiv:1404.3820v1 (Theorem 2.3, Proposition 2.2, Section 1.3).
- Michael A. Forbes, Amir Shpilka, Iddo Tzameret, Avi Wigderson, "Proof complexity lower bounds from algebraic circuit complexity", *31st Computational Complexity Conference (CCC 2016)*, LIPIcs 50, 2016, https://doi.org/10.4230/LIPIcs.CCC.2016.32; numbering of arXiv:1606.05050v1 (the Grochow-Pitassi simulation theorem and the remark following it, Section 1.1).
