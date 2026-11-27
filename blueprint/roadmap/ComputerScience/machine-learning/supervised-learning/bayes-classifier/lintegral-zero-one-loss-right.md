# Integrating the 0-1 loss over the prediction

Let $C$ be a measurable space with
measurable singletons, $\nu$ a measure on $C$ and $c \in C$, and let $\ell(c, y)$ be the 0-1
loss of predicting $y$ when the true class is $c$ ($0$ if $y = c$, $1$ otherwise). Then
$\int_C \ell(c, y)\,\nu(dy) = \nu(C \setminus \{c\})$.

When $\nu$ is the law of a random prediction, this is its expected 0-1 loss when the true class
is $c$.
