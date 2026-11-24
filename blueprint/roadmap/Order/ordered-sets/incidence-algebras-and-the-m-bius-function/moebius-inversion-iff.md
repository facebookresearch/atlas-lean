# Möbius inversion formula

Let $P$ be a poset in which every principal order ideal $\Lambda_t = \{s : s \le t\}$ is finite, let
$\mu$ be its Möbius function, and let $f, g \colon P \to K$ take values in a ring $K$. Then

$$g(t) = \sum_{s \le t} f(s) \ \text{for all } t \in P
\quad\Longleftrightarrow\quad
f(t) = \sum_{s \le t} g(s)\, \mu(s, t) \ \text{for all } t \in P.$$

No least element is assumed, so the formula applies to every finite poset. Stanley states it over a
field; the proof only uses that $\mu$ is a two-sided inverse of the zeta function, so any ring
works.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Proposition 3.7.1.
