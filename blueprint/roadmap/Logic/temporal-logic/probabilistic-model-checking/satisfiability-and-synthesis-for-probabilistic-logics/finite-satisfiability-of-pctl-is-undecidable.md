# Finite satisfiability of PCTL is undecidable

Whether a formula of probabilistic computation tree logic has a finite Markov chain as a model is undecidable, already for formulas $\varphi_1 \wedge \mathbf{G}_{=1}\varphi_2$ whose parts look at most two steps ahead; consequently validity over finite Markov chains is not even semi-decidable.

**Setting.** Formulas are those of [PCTL](../pctl.md) over a set of atomic propositions, with state formulas $\varphi ::= a \mid \neg\varphi \mid \varphi_1 \wedge \varphi_2 \mid P(\Phi) \bowtie r$ and path formulas $\Phi ::= \mathbf{X}\varphi \mid \varphi_1\,\mathbf{U}\,\varphi_2 \mid \varphi_1\,\mathbf{U}^{k}\varphi_2$, where ${\bowtie} \in \{\geq, >, \leq, <, =\}$, $r \in [0,1]$ is rational and $k \in \mathbb{N}$; $\mathbf{F}^k\varphi = \mathit{true}\,\mathbf{U}^k\varphi$, and $\mathbf{G}_{=1}\varphi$ abbreviates $P(\mathbf{F}\neg\varphi) = 0$. Formulas are interpreted over Markov chains $M = (S, P, v)$ with $S$ finite or countably infinite, $\sum_{t} P(s,t) = 1$ for every $s$, and a valuation $v$ of the propositions; $M$ is a *model* of $\varphi$ if some state satisfies $\varphi$. The *finite satisfiability problem* asks whether a given formula has a model with finitely many states.

**Theorem (Chodil and Kučera).** The finite satisfiability problem for PCTL is undecidable. This holds already for formulas of the form $\varphi_1 \wedge \mathbf{G}_{=1}\varphi_2$ in which the truth of $\varphi_1$ and $\varphi_2$ at a state depends only on the states reachable from it in at most two transitions (in the arXiv version, $\varphi_1, \varphi_2$ use only the path connectives $\mathbf{X}$ and $\mathbf{F}^2$). Consequently, the problem whether a PCTL formula is valid in all finite Markov chains is not semi-decidable.

The arXiv version states more precisely that finite satisfiability is $\Sigma^0_1$-hard.

## Depends on

- [PCTL](../pctl.md)
- [Discrete-time Markov chains](../discrete-time-markov-chains.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof simulates a synchronized product of two one-counter Minsky machines, which is as powerful as a two-counter machine, by a PCTL formula $\Psi$. Counter values are represented by *characteristic vectors* of probabilities, and increment and decrement become two fixed transformations of such vectors. A fixed formula with subformulas $\mathbf{X}_{=x}a$ and $\mathbf{X}_{=y}b$ forces arbitrarily large finite models just by changing the constants $x, y$. Then $\Psi$ is constructed so that every state satisfying it simulates the product machine, and every computation of the machine is covered by a model, which is finite when the computation is periodic. For deterministic machines the computation is periodic iff the machine is bounded, and boundedness of deterministic two-counter machines is $\Sigma^0_1$-complete, so $\Psi$ is finitely satisfiable iff the machine is bounded. A complete expansion links a page for the $\Sigma^0_1$-completeness of boundedness of deterministic two-counter machines (Section 2.3 and Proposition 6.1 of arXiv:2404.10648v1).

## Sources

- M. Chodil and A. Kučera, "The finite satisfiability problem for PCTL is undecidable", in *Proceedings of the 39th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2024)*, ACM, 2024, pp. 1–14, doi:10.1145/3661814.3662145; journal version *Journal of the ACM* 73(1):1–30, 2026, doi:10.1145/3787496 (both support the undecidability, the two-step fragment and the non-semi-decidability of finite validity, as stated in their abstracts).
- M. Chodil and A. Kučera, "The general and finite satisfiability problems for PCTL are undecidable", read as arXiv:2404.10648v1, <https://arxiv.org/abs/2404.10648v1>: Section 2 (PCTL, Markov chains and the satisfiability problems), Section 2.3 (Minsky machines and their boundedness problem), Section 6 (Proposition 6.1, Theorem 6.2 on simulating synchronized products of one-counter machines, and Corollary 6.3, $\Sigma^0_1$-hardness of finite satisfiability), and the introduction (the $\mathbf{X}$, $\mathbf{F}^2$ fragment) of arXiv:2404.10648v1.
