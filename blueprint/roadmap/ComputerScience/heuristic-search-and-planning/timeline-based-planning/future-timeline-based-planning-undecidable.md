# Future timeline-based planning over dense time is undecidable

In timeline-based planning, the behavior of state variables over real time is constrained by synchronization rules relating the start and end times of tokens. Deciding whether a plan exists is undecidable over dense time even when every trigger rule may only look forward in time from its trigger, already with one state variable.

**Setting (Bozzelli, Molinari, Montanari and Peron).** Let $\mathit{Intv}$ be the set of intervals of nonnegative reals with endpoints in $\mathbb{N} \cup \{\infty\}$, and $\mathit{Intv}_{(0,\infty)}$ those that are unbounded or left-closed with left endpoint $0$. A *state variable* $x = (V_x, T_x, D_x)$ has a finite domain $V_x$, a successor function $T_x : V_x \to 2^{V_x}$ and a duration constraint $D_x : V_x \to \mathit{Intv}$. A *timeline* for $x$ is a nonempty finite sequence of tokens $(v_0, d_0) \cdots (v_n, d_n)$ with real durations $d_i \in D_x(v_i)$ and $v_{i+1} \in T_x(v_i)$; token $i$ starts at $d_0 + \dots + d_{i-1}$ and ends at $d_0 + \dots + d_i$. *Atoms* constrain the difference between start or end times of two named tokens to lie in an interval, or compare such a time with a natural constant. An *existential statement* $\exists o_1[x_1 = v_1] \cdots \exists o_n[x_n = v_n].\, C$ asks for tokens with the given values satisfying the conjunction $C$ of atoms. A *trigger rule* $o_0[x_0 = v_0] \to E_1 \vee \dots \vee E_k$ requires that for every token of $x_0$ with value $v_0$ some $E_i$ holds with $o_0$ naming that token, and a trigger-less rule $\top \to E_1 \vee \dots \vee E_k$ requires some $E_i$ to hold. A trigger rule is satisfied *under the future semantics* if moreover all tokens chosen by the existential statements start no earlier than the trigger token. A *TP domain* $(SV, R)$ is a finite set of state variables with a finite set of rules; the *future TP problem* asks whether some assignment of a timeline to each variable satisfies all trigger-less rules and all trigger rules under the future semantics.

**Theorem (Bozzelli, Molinari, Montanari and Peron).** The future TP problem is undecidable, already for domains with one state variable whose intervals all lie in $\mathit{Intv}_{(0,\infty)}$.

Over dense time, timeline-based planning in general was already known to be undecidable, and restricting to simple trigger rules alone does not help either; with both restrictions together, future semantics and simple trigger rules, the problem becomes decidable.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof gives a polynomial-time construction that, from a two-counter Minsky machine $M$, builds a domain $P = (\{x_M\}, R_M)$ with one state variable, such that $M$ halts exactly when $P$ has a future plan. The untimed part of a future plan spells a computation-code of $M$: a sequence of configuration-codes, each consisting of a token recording the transition used and, for each counter, a block of tokens whose length is the counter value. Trigger rules force consecutive transition tokens to start exactly one time unit apart, and match each counter token of a configuration with a token of the next configuration whose start and end times are exactly one unit later; an increment or decrement shifts one token into or out of the block. Such punctual constraints are written as pairs of atoms with intervals in $\mathit{Intv}_{(0,\infty)}$, and the density of time lets arbitrarily large counter values fit in a bounded time window. Trigger-less rules require a token for the initial transition and one for a transition into the halting location.

## Sources

- Laura Bozzelli, Alberto Molinari, Angelo Montanari and Adriano Peron, *Undecidability of Future Timeline-based Planning over Dense Temporal Domains*, Proceedings of the 21st Italian Conference on Theoretical Computer Science (ICTCS 2020), CEUR Workshop Proceedings 2756, 2020, pp. 155–166, https://ceur-ws.org/Vol-2756/paper_15.pdf; Definitions 1–6, Theorem 1 and Proposition 1 of that open-access copy, whose numbering is used here; also read in arXiv:1904.09184v1, where the same results are Theorem 7 and Proposition 8.
