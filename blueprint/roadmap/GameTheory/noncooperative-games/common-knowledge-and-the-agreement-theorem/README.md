# Common knowledge and the agreement theorem

In Aumann's partition model of differential information, a finite set of states of the world carries a common prior and one information partition per agent; at each state an agent learns the cell of its partition that contains the state, and knows an event when that cell lies inside it. An event is common knowledge when it contains the cell of the meet (finest common coarsening) of the partitions, which is equivalent to every finite statement "agent $i_1$ knows that agent $i_2$ knows that … $E$" holding. Aumann's agreement theorem (1976) says that agents with a common prior whose posteriors for an event are common knowledge have equal posteriors: they cannot agree to disagree. Geanakoplos and Polemarchakis (1982) showed that communicating posteriors back and forth leads to such common knowledge, and hence to agreement, in finitely many rounds.

## Knowledge and common knowledge

- [Information cell](cell.md)
- [Knowledge operator](knows.md)
- [What is known is true](knows-subset.md)
- [Common knowledge](is-common-knowledge-at.md)
- [Iterated knowledge along a chain of agents](knows-chain.md)
- [Common knowledge as iterated knowledge](is-common-knowledge-at-iff-forall-knows.md)
- [Common knowledge is constant on the cells of the meet](is-common-knowledge-at-of-meet-rel.md)
- [Common knowledge is known by everyone](is-common-knowledge-at-mem-knows.md)
- [Values of commonly known functions are common knowledge](is-common-knowledge-at-level-set.md)

## The agreement theorem

- [Posterior probability](posterior.md)
- [Posteriors are conditional probabilities](posterior-eq-cond.md)
- [The tower step of the agreement theorem](measure-real-inter-cell-eq-mul.md)
- [Agreement theorem](agreement.md)
- [Agreeing to disagree](agreeing-to-disagree.md)

## Dialogues of posteriors

- [One round of public announcement of posteriors](dialogue-step.md)
- [Dialogue of posteriors](dialogue.md)
- [Partitions only get finer during a dialogue](dialogue-antitone.md)
- [At a fixed point of the dialogue, posteriors agree](posterior-eq-of-dialogue-step-eq.md)
- [We can't disagree forever](geanakoplos-polemarchakis.md)

## Summing over the cells of a partition

- [Information cell as a finset](cell-finset.md)
- [Averaging cell sums](sum-eq-sum-inv-card-mul-sum-cell.md)
- [Summing over the cells (equality)](sum-eq-zero-of-forall-sum-cell-eq-zero.md)
- [Summing over the cells (inequality)](sum-nonpos-of-forall-sum-cell-nonpos.md)

## Related topics

- [Correlated equilibria](../correlated-equilibria/README.md): Aumann's Main Theorem (1987) uses the same partition model with a common prior to derive correlated equilibrium from Bayes rationality.
- [Epistemic logic](../../../Logic/modal-logic/epistemic-logic/README.md): the syntactic side of knowledge, multi-agent S5 on Kripke models; equivalence relations there play the role of information partitions here.
- [Bayesian statistics](../../../Probability/bayesian-statistics/README.md): priors and posteriors, the probabilistic setting of the agreement theorem.
- [Revelation principle](../../mechanism-design/revelation-principle/README.md): Bayesian games and mechanisms with private information use the same common-prior model of beliefs.
