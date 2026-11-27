# Model checking order-1 PHFL is Π¹₁-hard and Σ¹₁-hard

With fixpoint alternation, model checking finite Markov chains against order-1 PHFL formulas is both Π¹₁-hard and Σ¹₁-hard, hence not in the arithmetical hierarchy.

**Theorem (Mitani, Kobayashi and Tsukada).** The model-checking problem for order-1 [PHFL](probabilistic-higher-order-fixpoint-logic.md) over finite Markov chains, given a finite Markov chain $M$ and a closed order-1 formula $\varphi$ of type $\mathrm{Prop}$, decide whether $M \models \varphi$, is $\Pi^1_1$-hard and $\Sigma^1_1$-hard.

## Depends on

- [Probabilistic higher-order fixpoint logic](probabilistic-higher-order-fixpoint-logic.md)

## Proof depends on

None.

## Expansion

The proof translates the order-1 fragment of higher-order fixpoint arithmetic, which extends Lubarsky's $\mu$-arithmetic (first-order arithmetic over $0$, successor and $\le$ with least and greatest fixpoints of predicates on natural numbers) by $\lambda$-abstraction, into order-1 PHFL. A fixed Markov chain $M$ with four states is used, on which natural numbers and the arithmetic operations are represented by quantitative propositions, and every arithmetic formula $\varphi$ of type $\Omega$ is mapped to a PHFL formula $\mathrm{tr}(\varphi)$ of the same order with $\varphi$ true iff $M \models \mathrm{tr}(\varphi)$ (Theorem 4.8, Corollary 4.9). Validity of first-order fixpoint arithmetic is $\Pi^1_1$-hard and $\Sigma^1_1$-hard (Theorem 4.5 of the source), which the source describes as probably folklore and derives from the $\Pi^1_1$-completeness of fair termination of programs (Harel) and the reduction of fair termination to validity of fixpoint arithmetic formulas. As an upper bound, $\mu$-arithmetic-definable predicates lie in $\Delta^1_2$ (Lubarsky).

## Sources

- Y. Mitani, N. Kobayashi and T. Tsukada, "A Probabilistic Higher-order Fixpoint Logic", *Logical Methods in Computer Science* 17(4), 2021, paper 15, pp. 15:1–15:36, <https://doi.org/10.46298/lmcs-17(4:15)2021>; numbers from arXiv:2011.14303v4, <https://arxiv.org/abs/2011.14303v4>: Section 4: Theorem 4.1, Theorem 4.5, Remark 4.6 and Corollary 4.9.
