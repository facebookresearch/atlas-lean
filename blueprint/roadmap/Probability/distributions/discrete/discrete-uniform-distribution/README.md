# Discrete uniform distribution

For a nonempty finite subset $s$ of a set $\alpha$, the uniform distribution on $s$ is the probability mass function on $\alpha$ that gives mass $1/|s|$ to each element of $s$ and mass $0$ to every other element of $\alpha$; nonemptiness makes the masses sum to $1$. Taking $s$ to be the whole of a nonempty finite set $\alpha$ gives the uniform distribution on $\alpha$, under which every event $A \subseteq \alpha$ has probability $|A| / |\alpha|$.

## Idea

The discrete uniform distribution models a choice in which no outcome is favoured: a fair die, a card from a well-shuffled deck, a random element of a finite set. Probabilities become counts, as in the classical definition: favourable outcomes divided by possible outcomes. For a fair die, $s = \{1, \dots, 6\}$, each face has probability $1/6$ and the event "the face is even" has probability $3/6 = 1/2$. Defining the law on a subset $s$, rather than only on a whole finite set, places it inside a larger space of outcomes, the points outside $s$ receiving no mass.

## Statements

- [Uniform distribution on a finite set](uniform-finset.md)
- [Uniform distribution on a finite type](uniform-fintype.md): special case: the whole finite type
- [Uniform distribution on the whole finite type](uniform-finset-univ.md): special case: the whole finite type
- [Outer measure of an event under the uniform distribution](to-outer-measure-uniform-fintype-apply.md): formula for events, outer-measure form
- [Probability of an event under the uniform distribution](to-measure-uniform-fintype-apply.md): formula for events: favourable over possible cases
