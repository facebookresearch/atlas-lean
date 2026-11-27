# Monotone LK polynomially simulates LK on monotone sequents

Every proof in Gentzen's propositional sequent calculus LK of a monotone sequent can be turned, with only polynomial growth in size, into a proof in monotone LK (MLK), where every formula is built from variables and constants with conjunction and disjunction only. This improves the quasipolynomial simulation of Atserias, Galesi and Pudlák.

An LK proof is a list of sequents $\varphi_1, \dots, \varphi_n \to \psi_1, \dots, \psi_m$, read as $\bigwedge_i \varphi_i \to \bigvee_j \psi_j$. The initial sequents are $\varphi \to \varphi$, $\Gamma \to 1$ and $0 \to \Gamma$ for any list $\Gamma$ of formulas. The rules are the left and right introduction rules for $\wedge$, $\vee$ and $\neg$, the cut rule (from $\Gamma \to \Delta, \varphi$ and $\varphi, \Gamma' \to \Delta'$ infer $\Gamma, \Gamma' \to \Delta, \Delta'$), and the structural rules of weakening, contraction and exchange. A formula is **monotone** (positive) if it is built over the basis $\wedge, \vee$ without $\neg$, and a sequent is monotone if all its formulas are. **MLK** is the subsystem of LK in which every formula in the proof is monotone. The size of a proof is the number of symbols in it.

**Theorem.** MLK polynomially simulates LK on monotone sequents: there is a polynomial $q$ such that every monotone sequent with an LK proof of size $S$ has an MLK proof of size at most $q(S)$.

Since the intuitionistic propositional sequent calculus LJ polynomially simulates MLK, LJ also polynomially simulates LK on monotone sequents. Monotone tautologies with polynomial-size LK proofs, such as the pigeonhole principle and the clique-colouring tautologies, therefore have polynomial-size MLK proofs. Whether tree-like MLK polynomially simulates MLK remains open.

## Expansion

By a lemma of Atserias, Galesi and Pudlák, MLK polynomially simulates LK on monotone sequents as soon as there are polynomial-size monotone threshold formulas $\mathrm{TH}^n_k(x_1, \dots, x_n)$ (true when at least $k$ inputs are 1) such that the sequents $\mathrm{TH}^n_k(\vec{x}) \to 0$ and $1 \to \mathrm{TH}^n_0(\vec{x})$ for $k > n$, and $\mathrm{TH}^n_k(x_1, \dots, x_i/0, \dots, x_n) \to \mathrm{TH}^n_{k+1}(x_1, \dots, x_i/1, \dots, x_n)$ for $0 \le k, i \le n$, have polynomial-size LK proofs. The natural divide-and-conquer threshold formulas are only quasipolynomial, which is the source of the earlier quasipolynomial bound.

Monotone threshold formulas of polynomial size come from the logarithmic-depth AKS sorting networks (in Paterson's variant). Jeřábek showed that their properties are provable in the theory $VNC^{1*}$ of $NC^1$ reasoning, whose proofs translate into polynomial-size LK proofs, provided that for some constant $D$ there is a parameter-free $NC^{1*}$ function $G(m)$ which $VNC^{1*}$ proves to be a $\langle 1/600, D \rangle$ bipartite $m + m$ expander for all $m$; under that hypothesis MLK polynomially simulates LK on monotone sequents. The provable construction of bipartite vertex expanders in the weaker theory $VNC^1$, applied with $\alpha = 1/600$, discharges this hypothesis, and the theorem follows.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

- [Edge expanders exist provably in $VNC^1$](vnc1-proves-existence-of-edge-expanders.md)

## Sources

- Sam Buss, Valentine Kabanets, Antonina Kolokolova, Michal Koucký, "Expander construction in $VNC^1$", *Annals of Pure and Applied Logic*, 2020, doi:10.1016/j.apal.2020.102796 (Theorem 1.2 = Theorem 7.3; Lemma 7.1 and Theorem 7.2 for the reduction; LK and MLK in Section 2.4; numbering of the authors' full version dated 7 November 2016, the edition read).
