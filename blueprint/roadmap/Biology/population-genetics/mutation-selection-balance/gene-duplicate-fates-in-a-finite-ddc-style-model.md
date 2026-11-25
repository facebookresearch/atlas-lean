# Fates of a duplicated gene in a finite duplication–degeneration–complementation model

Fix $z\ge1$ subfunctions and two gene copies $\{1,2\}$. A state is a tuple $S=(S_1,\ldots,S_z)$ of nonempty sets $S_j\subseteq\{1,2\}$, where $S_j$ is the set of copies that still perform subfunction $j$. The process is the continuous-time Markov chain on this finite state space with the following transitions:

- for each $j$ and each copy $c\in S_j$, at rate $\lambda>0$ copy $c$ loses subfunction $j$: $S_j\mapsto S_j\setminus\{c\}$;
- optionally, for each copy $c$, at rate $\nu\ge0$ a null mutation removes $c$ from every $S_j$ at once;
- a transition that would make some $S_j$ empty (loss of an essential subfunction) is suppressed: it does not occur.

There are no gains or back mutations. Classify states into three disjoint classes:

- *nonfunctionalized*: some copy belongs to no $S_j$;
- *subfunctionalized*: every $S_j$ is a singleton and each copy is the sole carrier of at least one subfunction;
- *transient*: some $S_j=\{1,2\}$ (then both copies carry a subfunction).

These classes partition the state space. The nonfunctionalized and subfunctionalized states are absorbing, and every transient state has an allowed transition. The initial state $S_j=\{1,2\}$ for all $j$ is transient. Every allowed transition strictly decreases the number of pairs $(j,c)$ with $c\in S_j$, so the chain is absorbed after finitely many jumps almost surely, and the probabilities of absorption in the nonfunctionalized and in the subfunctionalized class sum to $1$. These absorption probabilities are those of the embedded jump chain and solve the corresponding linear equations (equivalently, are given by its fundamental matrix). For $z=1$ the duplicate is nonfunctionalized with probability $1$.

## Depends on

- [Path of a continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Proof depends on

- [Mutation transition on allele frequencies](mutation-transition-on-allele-frequencies.md)
- [Backward equations for the mean hitting time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/ctmc-hitting-time-backward.md)

## Expansion

A full proof page must establish:

- The three classes are disjoint and exhaustive; absorption of the two fate classes under the suppression rule; existence of an allowed transition from every transient state.
- The initial state is transient, not nonfunctionalized.
- Almost-sure absorption from the strictly decreasing membership count, and absorption probabilities summing to $1$.
- For $z=1$, the only allowed transitions from $\{1,2\}$ lead to a state where one copy carries nothing.
- Absorption probabilities through the embedded jump chain and its [absorption equations](../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md), or through the continuous-time hitting-time equations.

## Sources

- M. Lynch and A. Force, *The probability of duplicate gene preservation by subfunctionalization*, Genetics (2000), <https://pubmed.ncbi.nlm.nih.gov/10629003/> (the subfunctionalization model; background).
