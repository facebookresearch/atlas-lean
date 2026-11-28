# Balancing of deconfined global types is undecidable

No algorithm decides whether a type configuration, a regular deconfined global type together with a finite queue of pending messages, is balanced. The same holds for weak balancing. The proof encodes the non-acceptance problem of queue machines.

**Theorem (Dagnino, Giannini and Dezani-Ciancaglini).** The following problem is undecidable: given a regular global type $\mathsf{G}$ (presented by a finite system of equations) and a message queue $\mathcal{M}$, does $\vdash \mathsf{G} \parallel \mathcal{M}$ hold, that is, is the type configuration $\mathsf{G} \parallel \mathcal{M}$ balanced?

The paper states that the proof adapts to weak balancing by deleting the readability side conditions, so weak balancing is undecidable as well.

## Depends on

- [Balanced type configurations of deconfined global types](balanced-global-type-configurations.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A queue machine $M = \langle Q, \Sigma, \Gamma, \triangleleft, s, \delta \rangle$ has initial queue symbol $\triangleleft \in \Gamma \setminus \Sigma$ and a total transition function $\delta : Q \times \Gamma \to Q \times \Gamma^\ast$: in configuration $\langle q, a\alpha \rangle$ it pops $a$, enters $q'$ and appends $\beta$, where $\delta(q, a) = \langle q', \beta \rangle$; it halts exactly when the queue is empty, and accepts $\gamma \in \Sigma^\ast$ if it halts from $\langle s, \gamma\triangleleft \rangle$. Queue machines are Turing complete, so acceptance is undecidable. For each state $q$ the reduction defines, between two participants $\mathsf{p}$ (sender) and $\mathsf{q}$ (receiver) with the queue alphabet as labels,

$$
\mathsf{G}_q = ?\{a;\ !b^a_1; \dots; !b^a_{n_a}; \mathsf{G}_{q'}\}_{a \in \Gamma} \quad \text{where } \delta(q, a) = \langle q', b^a_1 \cdots b^a_{n_a} \rangle,
$$

so $\mathsf{G}_q$ reads one symbol and writes the symbols the machine appends. Theorem 5.3 of the arXiv version shows that $M$ does not accept $\gamma$ if and only if $\mathsf{G}_s \parallel \gamma\triangleleft$ is balanced: a diverging run yields an infinite balancing derivation, and a halting run reaches an input with an empty queue, which no rule can derive. Hence balancing decides non-acceptance. The global types built by the reduction have two participants, one only sending and the other only receiving. A good expansion links a page for the undecidability of acceptance for queue machines, the problem the reduction starts from.

## Sources

- Francesco Dagnino, Paola Giannini and Mariangiola Dezani-Ciancaglini, "Deconfined Global Types for Asynchronous Sessions", Logical Methods in Computer Science 19(1), Article 3, 2023, <https://doi.org/10.46298/lmcs-19(1:3)2023>; Corollary 5.7 (balancing is undecidable), Theorem 5.3 (the reduction), Definitions 5.1 and 5.2 (queue machines and acceptance) and the remark after Corollary 5.7 (weak balancing) of arXiv:2111.11984v6, <https://arxiv.org/abs/2111.11984v6>.
