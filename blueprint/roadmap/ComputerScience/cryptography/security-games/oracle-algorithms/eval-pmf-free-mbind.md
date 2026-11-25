# Randomized run of a composition of computations

Let $O$ be a randomized oracle, $c$ an oracle computation and $f$ a function from its outputs to
oracle computations with outputs of any type. Running against $O$ the computation that runs $c$ and
continues with $f(x)$ on its output $x$ draws $x$ from the run of $c$ and then draws from the run of
$f(x)$.
