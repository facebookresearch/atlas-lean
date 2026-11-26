# Chebyshev-type count bound from the sum of squares

Let $S$ be a finite set, $f : S \to \mathbb Z$ and $s \ge 0$ an integer. Then

$$\#\{x \in S : f(x) \ge s\} \cdot s^2 \le \sum_{x \in S} f(x)^2 .$$

This is Markov's inequality for $f^2$ under the counting measure on $S$: each point counted on the left contributes at least $s^2$ to the right.

## Background

- [First moment method](../first-and-second-moment-methods/measure-real-one-le-le-integral.md): the same Markov step in probabilistic form.
