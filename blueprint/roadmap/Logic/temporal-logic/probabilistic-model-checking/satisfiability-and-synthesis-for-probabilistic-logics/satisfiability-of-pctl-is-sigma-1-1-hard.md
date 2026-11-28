# Satisfiability of PCTL is Σ¹₁-hard

Whether a formula of probabilistic computation tree logic has a model, a possibly infinite Markov chain, is $\Sigma^1_1$-hard, so beyond the arithmetical hierarchy, already when the only path connectives are $\mathbf{F}$ and $\mathbf{G}$; validity is $\Pi^1_1$-hard, and no sound and complete deductive system exists.

**Setting (Chodil and Kučera).** Formulas are those of [PCTL](../pctl.md) over a set of atomic propositions: state formulas $\varphi ::= a \mid \neg\varphi \mid \varphi_1 \wedge \varphi_2 \mid P(\Phi) \bowtie r$ and path formulas $\Phi ::= \mathbf{X}\varphi \mid \varphi_1\,\mathbf{U}\,\varphi_2 \mid \varphi_1\,\mathbf{U}^{k}\varphi_2$, with ${\bowtie} \in \{\geq, >, \leq, <, =, \neq\}$, $r \in [0,1]$ rational and $k \in \mathbb{N}$. They are interpreted over Markov chains $M = (S, \mathrm{Prob}, v)$ with a *finite or countably infinite* set of states $S$ ([discrete-time Markov chains](../discrete-time-markov-chains.md)), where $s \models P(\Phi) \bowtie r$ when the probability of the runs from $s$ satisfying $\Phi$ is $\bowtie r$. A formula $\varphi$ is *satisfiable* if $s \models \varphi$ for some state $s$ of some Markov chain, and *valid* if it holds in every state of every Markov chain. The *$\mathbf{F},\mathbf{G}$-fragment* allows only the path connectives $\mathbf{F}\varphi = \mathit{true}\,\mathbf{U}\,\varphi$ and $\mathbf{G}\varphi = \neg\mathbf{F}\neg\varphi$.

**Theorem (Chodil and Kučera).** The satisfiability problem for the $\mathbf{F},\mathbf{G}$-fragment of PCTL is $\Sigma^1_1$-hard, and the finite satisfiability problem (existence of a model with finitely many states) for this fragment is $\Sigma^0_1$-hard. Consequently, validity for the $\mathbf{F},\mathbf{G}$-fragment is $\Pi^1_1$-hard and finite validity is $\Pi^0_1$-hard (Theorem 8 of arXiv:2504.19207v2). Here a set of natural numbers is $\Sigma^1_1$-hard if every set definable by a formula $\exists f\, \forall n\, R(f, n, x)$ of second-order arithmetic, with $f$ ranging over functions $\mathbb N \to \mathbb N$ and $R$ recursive, many-one reduces to it, and $\Pi^1_1$-hard if its complement is $\Sigma^1_1$-hard; such sets are not in the arithmetical hierarchy.

PCTL does not have the small model property: some satisfiable formulas have no finite model. The undecidability of finite satisfiability of PCTL was shown earlier by the same authors ([finite satisfiability of PCTL is undecidable](finite-satisfiability-of-pctl-is-undecidable.md)). Satisfiability of the qualitative fragment, with probability constraints restricted to $=0$, $>0$, $=1$ and $<1$, is EXPTIME-complete, as the source recalls.

## Depends on

- [PCTL](../pctl.md)
- [Discrete-time Markov chains](../discrete-time-markov-chains.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The proof encodes the existence of a recurrent computation of a non-deterministic two-counter Minsky machine $\mathcal{M}$, a $\Sigma^1_1$-complete problem (Harel), by an effectively constructible formula $\varphi_{\mathcal{M}}$. Counter values are represented by pairs of probabilities: for a suitable $\vec z \in (0,1)^2$ and a function $\mathrm{INC} : (0,1)^2 \to (0,1)^2$, the value $n$ is represented by $\mathrm{INC}^n(\vec z)$; a geometric theorem (Theorem 5 of the source) shows that every countable set of pairs closed under the decrement in the sense of convex combinations lies in a region where this representation is faithful, which lets PCTL formulas force exact simulation of increments, decrements and zero tests. Two one-counter simulations are synchronized into a two-counter machine (Propositions 6 and 7). Omitting the recurrence requirement and using a deterministic machine gives a formula with a finite model exactly when the machine has a bounded computation, whose $\Sigma^0_1$-completeness gives the finite clause. A complete expansion also links pages for the geometric representation theorem (Theorem 5 of the source) and for the $\Sigma^0_1$-completeness of boundedness of deterministic two-counter machines.

## Sources

- M. Chodil and A. Kučera, "The Satisfiability and Validity Problems for Probabilistic Computational Tree Logic are Highly Undecidable", in *52nd International Colloquium on Automata, Languages, and Programming (ICALP 2025)*, Leibniz International Proceedings in Informatics 334, Schloss Dagstuhl, 2025, pp. 151:1–151:20, doi:[10.4230/LIPIcs.ICALP.2025.151](https://doi.org/10.4230/LIPIcs.ICALP.2025.151); read as arXiv:2504.19207v2 ([arXiv](https://arxiv.org/abs/2504.19207v2)), whose numbering is used (one global counter; Proposition 2 recalls the Minsky-machine facts): Definition 1 and Section 2, Theorem 5, Propositions 6 and 7, Theorem 8 in Section 7, and the appendix on Minsky machines.
