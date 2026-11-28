# Full execution-time opacity strategy emptiness is undecidable

It is undecidable whether some strategy enabling controllable actions over time makes a timed automaton fully execution-time opaque, that is, gives the same set of durations for runs that visit the private location and runs that avoid it. Undecidability holds already for timed automata with a single clock.

**Theorem.** The full ET-opacity strategy emptiness problem is undecidable: there is no algorithm that, given a timed automaton $\mathcal{A}$ with a private location, final locations and a partition $\Sigma = \Sigma_c \uplus \Sigma_u$ of its actions into controllable and uncontrollable ones, decides whether there exists a strategy $\sigma : \mathbb{R}_{\ge 0} \to 2^{\Sigma_c}$ such that $\mathcal{A}$ is fully ET-opaque with $\sigma$, in the sense of [Execution-time opacity control of timed automata](execution-time-opacity-control.md). The problem remains undecidable for timed automata with one clock.

The proof applies whether or not strategies are required to be finitely varying, so that restriction does not regain decidability (Remark 2).

## Depends on

- [Execution-time opacity control of timed automata](execution-time-opacity-control.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces from termination of two-counter Minsky machines started with both counters at $0$, and builds a one-clock TA $\mathcal{A}$ that admits an opacity-enforcing strategy if and only if the machine does not terminate. Each command takes three time units: within each period, the first unit carries the value of the first counter, the second unit that of the second counter, and the third unit checks that the strategy kept the system opaque; no private run reaches the final location during the third unit. A counter with value $k$ is represented by $k$ public runs reaching the final location at distinct times of its unit; to stay opaque the strategy must enable a controllable action at exactly those instants, which yields a private run reaching the final location immediately and a public run reaching it three units later, so the counter value is carried to the next period. Gadgets for increment, decrement and zero test, and a gadget for the halting command that breaks opacity, are combined by an initial location with uncontrollable zero-time edges into them. If the machine does not terminate, a strategy emulating it (for instance enabling the first counter's action at times $1/2^n$ for $n$ up to the counter value) is opaque; if it terminates, any strategy either fails to emulate the machine or reaches the halting gadget, and opacity fails.

## Sources

- Étienne André, Marie Duflot, Laetitia Laversa and Engel Lefaucheux, "Execution-time opacity control for timed automata", *Software and Systems Modeling*, Springer, published online 2026 (no volume or pages in the publisher record read), doi:[10.1007/s10270-026-01395-5](https://doi.org/10.1007/s10270-026-01395-5); this extended version adds the undecidability result to the conference paper of the same title in *Software Engineering and Formal Methods (SEFM 2024)*, Lecture Notes in Computer Science 15280, pp. 347–365, 2024, doi:[10.1007/978-3-031-77382-2_20](https://doi.org/10.1007/978-3-031-77382-2_20). Read in arXiv:2409.10336v3 ([arXiv](https://arxiv.org/abs/2409.10336v3)), the extended version that adds this result to the conference paper (the first arXiv version, which matches the conference paper, has no undecidability theorem); the journal article, cited as its refereed version, was not read. Numbering of arXiv:2409.10336v3: Theorem 1 with its proof in Section 4, Remark 1 (one clock) and Remark 2 (finitely varying strategies).
