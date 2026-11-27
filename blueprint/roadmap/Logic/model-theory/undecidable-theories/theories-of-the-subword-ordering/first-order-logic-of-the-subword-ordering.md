# First-order logic of the subword ordering

The first-order logic of subwords $\mathrm{FO}(A^*, \sqsubseteq)$ speaks about the finite words over an alphabet $A$ ordered by the subsequence (scattered subword) ordering, in which $u \sqsubseteq v$ when $u$ is obtained from $v$ by deleting letters.

**Structure.** For a finite alphabet $A$, the domain is $A^*$ and $u \sqsubseteq v$ is true iff $u = a_1 \cdots a_n$ and $v \in A^* a_1 A^* \cdots A^* a_n A^*$.

**Logics.** The *pure logic* has $\sqsubseteq$ (and equality) as its only symbol; the *basic logic* adds every word $u \in A^*$ as a constant denoting itself. Formulas are first-order formulas over these signatures. The fragment $\mathrm{FO}^n$ consists of the formulas using at most $n$ distinct variables, and $\Sigma_n$, $\Pi_n$ are defined by quantifier alternation as usual ($\Sigma_2$ formulas are, up to equivalence, $\exists^*\forall^*$ formulas).

**Truth problem.** Given $A$ and a sentence $\phi$, decide whether $A^* \models \phi$. Unless the alphabet is fixed, $A$ is part of the input.

## Depends on

None.

## Proof depends on

None.

## Expansion

The truth of a pure-logic sentence may depend on $A$, but only through its size. Kuske showed that the $\Sigma_3$ theory is undecidable already for two letters and that the $\Sigma_1$ theory is decidable; the $\Sigma_1$ fragment is NP-complete, and the two-variable fragment $\mathrm{FO}^2$ is decidable and PSPACE-hard.

## Sources

- P. Karandikar and P. Schnoebelen, "Decidability in the logic of subsequences and supersequences", in *35th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2015)*, Leibniz International Proceedings in Informatics 45, Schloss Dagstuhl, 2015, pp. 84–97, doi:10.4230/LIPIcs.FSTTCS.2015.84; read as arXiv:1510.03994v1, <https://arxiv.org/abs/1510.03994v1>: Section 2 (the subword ordering, the pure and basic logics, the fragments $\mathrm{FO}^n$, $\Sigma_n$, $\Pi_n$, the truth problem and Theorem 2.1), Section 1 (Kuske's results) and Theorems 5.5–5.6.
