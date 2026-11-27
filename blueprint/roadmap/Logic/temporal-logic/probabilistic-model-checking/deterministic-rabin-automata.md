# Deterministic Rabin automata

A *deterministic Rabin automaton* (DRA) is a [Rabin automaton](../../../TheoryOfComputation/omega-automata-and-games/rabin-and-streett-automata/rabin.md) with one initial state whose transition relation is a total function; explicitly, it is a tuple $A = (Q, \bar q, \alpha_A, \delta_A, \mathit{Acc})$ of a finite set $Q$ of states, an initial state $\bar q$, a finite alphabet $\alpha_A$, a total transition function $\delta_A : Q \times \alpha_A \to Q$ and an acceptance condition $\mathit{Acc} = \{(L_i, K_i)\}_{i=1}^k$ with $L_i, K_i \subseteq Q$. Every infinite word $w = a_0 a_1 \cdots$ over $\alpha_A$ has a unique run $\bar q \xrightarrow{a_0} q_1 \xrightarrow{a_1} q_2 \cdots$, and $A$ accepts $w$ if for some $i$ the run contains finitely many states from $L_i$ and infinitely many from $K_i$; $L(A)$ is the set of accepted words. A pair $(L_i, K_i)$ here is the Rabin pair $(E, F) = (K_i, L_i)$ of the general definition. For every LTL formula $\psi$ there is a DRA $A_\psi$ with $w \models \psi \iff w \in L(A_\psi)$; DRAs capture exactly the $\omega$-regular properties, whereas deterministic Büchi automata do not suffice (for example for $\mathbf{F}\,\mathbf{G}\, a$).

## Depends on

- [Rabin automaton](../../../TheoryOfComputation/omega-automata-and-games/rabin-and-streett-automata/rabin.md)
- [Satisfaction of LTL formulas on ω-words](../linear-temporal-logic/satisfies.md)

## Proof depends on

- [No deterministic Büchi automaton accepts "eventually always 0"](../../../TheoryOfComputation/omega-automata-and-games/b-chi-automata-for-infinitely-often-and-eventual/not-exists-da-buchi-eventually-zero.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 7.2, Definition 21 and the discussion after it.
