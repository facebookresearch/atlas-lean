# First-order logic of the subword ordering

The first-order logic of subwords $\mathrm{FO}(A^*, \sqsubseteq)$ speaks about the finite words over an alphabet $A$ ordered by the subsequence (scattered subword) ordering, in which $u \sqsubseteq v$ when $u$ is obtained from $v$ by deleting letters.

**Structure.** For a finite alphabet $A$, the domain is $A^*$ and $u \sqsubseteq v$ is true iff $u = a_1 \cdots a_n$ and $v \in A^* a_1 A^* \cdots A^* a_n A^*$.

**Logics.** The *pure logic* has $\sqsubseteq$ (and equality) as its only symbol; the *basic logic* adds every word $u \in A^*$ as a constant denoting itself. Formulas are first-order formulas over these signatures. The fragment $\mathrm{FO}^n$ consists of the formulas using at most $n$ distinct variables, and $\Sigma_n$, $\Pi_n$ are defined inductively, without prenex form (Section 2 of the source): atomic formulas are in every $\Sigma_n$ and $\Pi_n$; $\neg\varphi$ is in $\Sigma_n$ iff $\varphi$ is in $\Pi_n$, and in $\Pi_n$ iff $\varphi$ is in $\Sigma_n$; $\varphi \wedge \varphi'$ is in $\Sigma_n$ (resp. $\Pi_n$) iff both are; for $n > 0$, $\exists x\,\varphi$ is in $\Sigma_n$ iff $\varphi$ is, and, for $n \ge 2$, in $\Pi_n$ iff $\varphi$ is in $\Sigma_{n-1}$ (so no $\exists x\,\varphi$ is in $\Pi_1$); dually, $\forall x\,\varphi$ is in $\Pi_n$ iff $\varphi$ is, and, for $n \ge 2$, in $\Sigma_n$ iff $\varphi$ is in $\Pi_{n-1}$. This corrects the clauses as printed in Section 2 of the source (and in its FSTTCS 2015 version), which start the cross-quantifier clauses at $n = 1$ and would put $\forall x\,\psi$ in $\Sigma_1$ for quantifier-free $\psi$; with the correction, $\Sigma_1$ formulas are the existential ones, as in the source's results. In particular $\Sigma_2$ formulas are, up to equivalence, $\exists^*\forall^*$ formulas.

**Truth problem.** Given $A$ and a sentence $\phi$, decide whether $A^* \models \phi$. Unless the alphabet is fixed, $A$ is part of the input.

## Depends on

- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)

## Proof depends on

None.

## Expansion

The truth of a pure-logic sentence may depend on $A$, but only through its size. Kuske showed that the $\Sigma_3$ theory is undecidable already for two letters and that the $\Sigma_1$ theory is decidable; the $\Sigma_1$ fragment is NP-complete, and the two-variable fragment $\mathrm{FO}^2$ is decidable and PSPACE-hard.

## Sources

- P. Karandikar and P. Schnoebelen, "Decidability in the logic of subsequences and supersequences", in *35th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2015)*, Leibniz International Proceedings in Informatics 45, Schloss Dagstuhl, 2015, pp. 84–97, doi:10.4230/LIPIcs.FSTTCS.2015.84; read as arXiv:1510.03994v1, <https://arxiv.org/abs/1510.03994v1>: Section 2 (the subword ordering, the pure and basic logics, the fragments $\mathrm{FO}^n$, $\Sigma_n$, $\Pi_n$, the truth problem and Theorem 2.1), Section 1 (Kuske's results) and Theorems 5.5–5.6.
