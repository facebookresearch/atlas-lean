# Model checking order-1 PHFL is undecidable

Model checking finite Markov chains against the probabilistic higher-order fixpoint logic is undecidable, already for closed order-1 formulas without fixpoint alternation.

**Theorem (Mitani, Kobayashi and Tsukada).** There is no algorithm that, given a finite Markov chain $M$ and a closed order-1 formula $\varphi$ of type $\mathrm{Prop}$ of [PHFL](probabilistic-higher-order-fixpoint-logic.md), decides whether $M \models \varphi$. Undecidability holds already for the $\mu$-only order-1 fragment, without greatest fixpoints and hence without fixpoint alternation. The proof reduces the value-1 problem for probabilistic automata, undecidable by Gimbert and Oualhadj: from an automaton $\mathcal A$ it builds a finite Markov chain $M_{\mathcal A}$ and a formula $\varphi_{\mathcal A}$ with $M_{\mathcal A} \models \varphi_{\mathcal A}$ iff $\mathcal A$ has value 1 (Theorems 3.3 and 3.5 of the source).

By contrast, model checking finite Markov chains is decidable for the full $\mu^p$-calculus (order 0) and for non-probabilistic higher-order fixpoint logic, both with fixpoint alternation; the combination of probabilities and higher-order predicates causes the undecidability.

## Depends on

- [Probabilistic higher-order fixpoint logic](probabilistic-higher-order-fixpoint-logic.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The value-1 problem for probabilistic automata is undecidable](../../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/value-1-problem-for-probabilistic-automata.md)

## Proof sketch

The proof reduces the value-1 problem for probabilistic automata (Gimbert and Oualhadj): given an automaton $A$ with state set $Q$ and letters $c_1, \ldots, c_m$, is $\sup_w \Pr_A(w) = 1$? One builds a Markov chain $M_A$ and order-1 formulas $g_w$ of type $\mathrm{Prop}$, one per word, with $A_q(w)$, the acceptance probability of $w$ from $q$, equal to the value of $g_w$ at $q$ (Lemma 3.4). For the $\mu$-only order-1 formula $\theta_A = \mu F.\lambda X.\,X \vee \bigvee_{c \in \Sigma} F(f_c X)$, the value of $\theta_A\,p_F$ at the initial state is $\mathrm{val}(A)$, so $M_A \models [\theta_A\,p_F]_{\ge 1}$ iff $\mathrm{val}(A) = 1$ (Theorem 3.5). Since $\mathrm{val}(A)$ cannot even be approximated, the values of qualitative PHFL formulas are not approximately computable in general.

## Sources

- Y. Mitani, N. Kobayashi and T. Tsukada, "A Probabilistic Higher-order Fixpoint Logic", *Logical Methods in Computer Science* 17(4), 2021, paper 15, pp. 15:1–15:36, <https://doi.org/10.46298/lmcs-17(4:15)2021>; numbers from arXiv:2011.14303v4, <https://arxiv.org/abs/2011.14303v4>: Section 3: Theorem 3.3 (the value-1 problem), Lemma 3.4, Theorem 3.5, Corollary 3.6 and Remark 3.7.
