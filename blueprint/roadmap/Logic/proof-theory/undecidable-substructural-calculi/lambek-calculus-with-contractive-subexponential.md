# Lambek calculus with a contractive subexponential is undecidable

If at least one subexponential of the signature allows non-local contraction, derivability in the Lambek calculus with subexponentials is undecidable, already in its multiplicative fragment without the unit.

**Theorem (Kanovich, Kuznetsov, Nigam and Scedrov).** Let $\Sigma = \langle \mathcal{I}, \preceq, \mathcal{W}, \mathcal{C}, \mathcal{E} \rangle$ be a subexponential signature with $\mathcal{C} \neq \varnothing$. Then the derivability problem for each of the calculi $\mathrm{SLC}_\Sigma$, $\mathrm{SLC}^{\mathbf{1}}_\Sigma$ and $\mathrm{SMALC}_\Sigma$ of the [Lambek calculus with subexponentials](lambek-calculus-with-subexponentials.md) is undecidable: no algorithm decides, given a sequent $\Gamma \to C$ in the respective language, whether it is derivable. The signature $\Sigma$ is fixed; weakening and exchange need not be allowed for the contractive label.

The clauses come from Theorem 8 ($\mathrm{SLC}^{\mathbf{1}}_\Sigma$), Theorem 12 ($\mathrm{SLC}_\Sigma$) and Corollary 13 ($\mathrm{SMALC}_\Sigma$) of the source, which also derives undecidability of cyclic linear logic with subexponentials (Corollary 14). Conversely, if $\mathcal{C} = \varnothing$ the source shows that derivability in cyclic linear logic with subexponentials, into which $\mathrm{SMALC}_\Sigma$ embeds faithfully (Corollary 4), is in PSPACE (Theorem 15), so non-local contraction is what makes the problem undecidable.

## Depends on

- [Lambek calculus with subexponentials](lambek-calculus-with-subexponentials.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Reachability for string rewriting is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-sr.md)

## Expansion

The proof encodes semi-Thue systems, following earlier proofs for non-commutative linear logic with a full exponential (Lincoln, Mitchell, Scedrov and Shankar; Kanazawa; de Groote). By Markov and Post (Theorem 9 of the source) there is a fixed word rewriting system $P$ for which derivability $\gamma \Rightarrow^* \delta$ is undecidable. The rules of $P$ are turned into formulas, and Lemma 10 shows that $\gamma \Rightarrow^* \delta$ iff a sequent $\Phi, b_1, \dots, b_k \to a_1 \cdots a_l$ is derivable in $\mathrm{SLC}^{\mathbf{1}}_\Sigma$, where $\gamma = a_1 \cdots a_l$, $\delta = b_1 \cdots b_k$ and $\Phi$ is a fixed sequence of formulas built from the rule formulas with a contractive ${!}^s$; the unit is used so that the encoding works although the contractive label need not allow weakening. Lemma 11 then removes the unit: replacing $\mathbf{1}$ by $q / q$ and each variable $p_i$ by $(q / q) \cdot p_i \cdot (q / q)$, for a fresh $q$, preserves derivability, which gives the result for $\mathrm{SLC}_\Sigma$. Undecidability passes to $\mathrm{SMALC}_\Sigma$ because it is a conservative extension. A good expansion links a page for cut elimination for $\mathrm{SLC}^{\mathbf 1}_\Sigma$ and $\mathrm{SMALC}_\Sigma$ (Corollary 3 of the source), which the proof of Lemma 10 uses and which the definition page only asserts.

## Sources

- M. Kanovich, S. Kuznetsov, V. Nigam and A. Scedrov, "Subexponentials in non-commutative linear logic", *Mathematical Structures in Computer Science* 29(8):1217–1249, 2019, doi:10.1017/S0960129518000117; read as arXiv:1709.03607v1, <https://arxiv.org/abs/1709.03607v1>: Theorems 8 and 12 and Corollaries 13–14 of arXiv:1709.03607v1, with Theorem 9 and Lemmas 10–11 in Section 7, Corollary 4, and Theorem 15 in Section 8.
