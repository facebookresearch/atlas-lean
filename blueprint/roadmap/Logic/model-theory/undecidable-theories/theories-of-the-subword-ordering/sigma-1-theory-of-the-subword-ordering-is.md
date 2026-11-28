# The Σ₁ theory of the subword ordering with constants is undecidable

Whether an existential sentence about finite words ordered by the subsequence relation, with every word available as a constant, is true is undecidable already over a two-letter alphabet, and already when only three variables are not bounded in their number of letter alternations.

**Setting.** For a finite alphabet $A$, the [first-order logic of the subword ordering](first-order-logic-of-the-subword-ordering.md) with constants, $\mathrm{FO}(A^*, \sqsubseteq, w_1, \dots)$, has domain $A^*$, the subsequence ordering $\sqsubseteq$, and a constant for each word. Its $\Sigma_1$ fragment consists of the existential formulas $\exists x_1 \cdots \exists x_k\, \psi$ with $\psi$ quantifier-free. For $A = \{a_1, \dots, a_n\}$, a variable is *alternation bounded* if it ranges over $(a_1^* \cdots a_n^*)^\ell$ for some fixed $\ell \in \mathbb{N}$; the fragment $\Sigma_{1,3}$ consists of the $\Sigma_1$ formulas in which at most three variables are not alternation bounded. The *truth problem* asks whether a given sentence holds in $A^*$.

**Theorem (Halfon, Schnoebelen and Zetzsche).** Let $|A| \geq 2$ and $a \in A$. For every recursively enumerable set $S \subseteq \mathbb{N}$ there is a $\Sigma_{1,3}$ formula $\varphi(x)$ of $\mathrm{FO}(A^*, \sqsubseteq, w_1, \dots)$ whose set of solutions is $\{a^k : k \in S\}$. Consequently, for every fixed alphabet with at least two letters, the truth problem for $\Sigma_1$ sentences, and even for $\Sigma_{1,3}$ sentences, is undecidable.

The thresholds are sharp in the source's sense: the $\Sigma_{1,2}$ fragment is decidable, and if every variable is alternation bounded the full first-order theory is decidable.

## Depends on

- [First-order logic of the subword ordering](first-order-logic-of-the-subword-ordering.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By the Davis–Putnam–Robinson–Matiyasevich theorem, every r.e. set is the projection of the solutions of a finite system of equations of the forms $x_i = x_j + x_k$, $x_i = x_j \cdot x_k$, $x_i = 1$. Numbers are coded as words $a^k$, and the proof defines in $\Sigma_{1,3}$ the predicates needed to express such equations: membership in piecewise testable languages (quantifier-free with constants), and, using primitive words and the fact that $pw = wp$ forces $w \in p^*$ for primitive $p$, enough of concatenation to express addition and multiplication of exponents. Taking $S$ r.e. and not recursive gives undecidability. The arXiv version also shows, in an appendix, that a single constant $W \in \{a,b\}^*$ suffices for undecidability of $\Sigma_{1,3}$ truth. Earlier, the $\Sigma_2$ theory was known to be undecidable (Karandikar and Schnoebelen).

## Sources

- Simon Halfon, Philippe Schnoebelen and Georg Zetzsche, "Decidability, complexity, and expressiveness of first-order logic over the subword ordering", in *32nd Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2017)*, IEEE, 2017, pp. 1–12, doi:10.1109/LICS.2017.8005141; read as arXiv:1701.07470v2, <https://arxiv.org/abs/1701.07470v2>: Section 2 (subwords, the logics and the fragments $\Sigma_{i,j}$), the main theorem of Section 3.1 (the $\Sigma_{1,3}$ fragment) with its preceding statement of the DPRM theorem, and the abstract (decidability of $\Sigma_{1,2}$ and of the alternation-bounded theory) of arXiv:1701.07470v2.
