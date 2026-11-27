# The Σ₂ theory of the subword ordering is undecidable

Whether an $\exists^*\forall^*$ sentence about words ordered by the subsequence relation is true is undecidable, even with three variables, even without constants, and even for a fixed alphabet, answering a question of Kuske.

**Theorem (Karandikar and Schnoebelen).** For the [first-order logic of the subword ordering](first-order-logic-of-the-subword-ordering.md):

1. the truth problem for the basic logic (with constants for words) is undecidable even for sentences in the $\Sigma_2 \cap \mathrm{FO}^3$ fragment (Theorem 3.1);
2. the truth problem for the pure logic (with $\sqsubseteq$ only) is undecidable even for $\Sigma_2$ sentences, with the alphabet part of the input (Theorem 4.1);
3. there is a fixed alphabet $A$ such that the truth problem for $\Sigma_2$ sentences of the pure logic over $A^*$ is undecidable (Theorem 4.6).

In particular the $\mathrm{FO}^3$ theory is undecidable, whereas the $\Sigma_1$ theory (NP-complete) and the $\mathrm{FO}^2$ theory are decidable, so these thresholds are sharp.

## Depends on

- [First-order logic of the subword ordering](first-order-logic-of-the-subword-ordering.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Clause 1 encodes the Post correspondence problem. The key observation is that, in the basic logic, membership of a word in certain regular languages and the projection of a word onto a subalphabet can be defined by $\Sigma_2 \cap \mathrm{FO}^3$ formulas (Lemma 3.3); an instance $(u_1, v_1), \dots, (u_n, v_n)$ then has a solution iff there are words $x \in (1u_1 + \cdots + nu_n)^+$ and $x' \in (1v_1 + \cdots + nv_n)^+$ with equal projections onto the index letters $\{1, \dots, n\}$ and onto the PCP alphabet, which is a $\Sigma_2$ sentence. Clause 2 removes the constants: a $\Sigma_2$ formula of the pure logic defines all letters and the needed constant words up to an automorphism (mirroring) of the structure, using Simon's congruence (Lemmas 4.2 and 4.3). Clause 3 reduces instead from a variant of PCP that is undecidable for a fixed alphabet and fixed pairs, with only a prefix word as input (Lemma 4.5).

## Sources

- P. Karandikar and P. Schnoebelen, "Decidability in the logic of subsequences and supersequences", in *35th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2015)*, Leibniz International Proceedings in Informatics 45, Schloss Dagstuhl, 2015, pp. 84–97, doi:10.4230/LIPIcs.FSTTCS.2015.84; read as arXiv:1510.03994v1, <https://arxiv.org/abs/1510.03994v1>: Theorems 3.1, 4.1 and 4.6 of arXiv:1510.03994v1, with Lemmas 3.3, 4.2, 4.3 and 4.5.
