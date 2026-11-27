# Möbius inversion formula, dual form

Let $P$ be a poset in which every principal dual order ideal $V_s = \{t : t \ge s\}$ is finite, let
$\mu$ be its Möbius function, and let $f, g \colon P \to K$ take values in a ring $K$. Then

$$g(s) = \sum_{t \ge s} f(t) \ \text{for all } s \in P
\quad\Longleftrightarrow\quad
f(s) = \sum_{t \ge s} \mu(s, t)\, g(t) \ \text{for all } s \in P.$$

## Background

- [Möbius inversion formula](moebius-inversion-iff.md): the same statement for principal order
  ideals; the dual form is the case of the dual poset.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Proposition 3.7.2.
