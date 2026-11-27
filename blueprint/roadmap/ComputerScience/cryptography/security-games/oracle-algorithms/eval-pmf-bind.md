# Randomized run of a sequential composition

Let $O$ be a randomized oracle, $c$ an oracle computation and $f$ a function from its outputs to
oracle computations. Running against $O$ the composition that runs $c$ and then $f(x)$ on its output
$x$ gives the distribution obtained by drawing $x$ from the run of $c$ and then drawing from the run
of $f(x)$.
