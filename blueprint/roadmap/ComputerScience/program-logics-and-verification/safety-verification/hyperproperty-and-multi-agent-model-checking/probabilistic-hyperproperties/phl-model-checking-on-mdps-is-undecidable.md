# Model checking probabilistic hyperproperties of MDPs is undecidable

The logic PHL quantifies over schedulers of a Markov decision process and over paths of the induced Markov chains, and compares probabilities of LTL properties under the chosen schedulers. Its model checking problem is undecidable, already for formulas with existential scheduler quantifiers followed by universal path quantifiers and one probabilistic constraint.

**Setting (Dimitrova, Finkbeiner and Torfah).** An MDP $M = (S, \mathit{Act}, P, \iota, \mathit{AP}, L)$ has finitely many states and actions, transition probabilities $P(s, a, \cdot)$, an initial distribution and a labeling with atomic propositions; a scheduler maps finite histories to distributions over enabled actions and induces a Markov chain. PHL formulas over scheduler variables $\sigma$ and path variables $\pi : \sigma$ (a path of the chain induced by $\sigma$) are

$$
\Phi ::= \forall \sigma.\, \Phi \mid \Phi \wedge \Phi \mid \neg \Phi \mid \psi \mid E \bowtie c,
$$

where $\psi$ is a HyperCTL$^*$ formula over atoms $a_\pi$, built with $\wedge$, $\neg$, next, until and path quantifiers $\forall \pi : \sigma$; $E ::= \mathbb{P}(\varphi) \mid E + E \mid c \cdot E$ is a probability expression over LTL formulas $\varphi$ with atoms $a_\sigma$; $c \in \mathbb{Q}$ and $\bowtie$ is a comparison. The model checking problem asks, given a finite MDP and a closed well-formed PHL formula, whether the MDP satisfies it.

**Theorem (Dimitrova, Finkbeiner and Torfah).** The model checking problem for PHL is undecidable. It remains undecidable for formulas of the form

$$
\exists \sigma_1 \dots \exists \sigma_n.\ \bigl((\forall \pi_1 : \sigma_1 \dots \forall \pi_n : \sigma_n.\ \psi) \wedge E \bowtie c\bigr)
$$

and, dually, for formulas $\forall \sigma_1 \dots \forall \sigma_n.\ \bigl((\forall \pi_1 : \sigma_1 \dots \forall \pi_n : \sigma_n.\ \psi) \to E \bowtie c\bigr)$.

The schedulers range over all (history-dependent, randomized) schedulers. The paper gives approximate and bounded model checking procedures instead of an exact algorithm.

## Depends on

- [Markov decision processes and adversaries](../../../../../Logic/temporal-logic/probabilistic-model-checking/markov-decision-processes-and-adversaries.md)
- [Discrete-time Markov chains](../../../../../Logic/temporal-logic/probabilistic-model-checking/discrete-time-markov-chains.md)
- [Formulas of linear temporal logic](../../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [HyperCTL*](../../../../../Logic/temporal-logic/temporal-specification/hyperctl-star.md)

## Proof depends on

None.

## Expansion

The reduction is from emptiness of probabilistic Büchi automata (does some infinite word have positive acceptance probability), undecidable by Baier, Bertrand and Größer. From such an automaton one builds an MDP in which the scheduler picks the letters and the probabilistic transitions mimic the automaton. The formula asserts a scheduler under which all paths make the same choices, so that the scheduler is blind and generates one word $w$ regardless of the visited states, and under which accepting states are visited infinitely often with positive probability; this holds exactly when some word is accepted with positive probability. For the restricted forms two schedulers are used, one that builds the word and one that mimics the automaton. Emptiness of probabilistic Büchi automata has no page here.

## Sources

- Rayna Dimitrova, Bernd Finkbeiner and Hazem Torfah, "Probabilistic Hyperproperties of Markov Decision Processes", Automated Technology for Verification and Analysis (ATVA 2020), Lecture Notes in Computer Science 12302, pp. 484–500, Springer, 2020, <https://doi.org/10.1007/978-3-030-59152-6_27>; the syntax of Section 3, the undecidability theorem of the subsection "Undecidability of PHL Model Checking" with its proof, and the theorem and corollary of the appendix "Additional Undecidability Results" (the existential and universal forms) of arXiv:2005.03362v3 (the copy read), <https://arxiv.org/abs/2005.03362v3>.
