# Every failed training pass adds a mistake

Let $K$ be a commutative ring with a linear
order and $\iota$ a finite type, and let $L$ be a finite list of labelled examples $(x, y)$ with
$x \in K^\iota$ and $y$ a Boolean. For every natural number $n$ and all weights $w \in K^\iota$, if
training on $L$ from $w$ with at most $n$ passes returns no weights, then the perceptron run from
$w$ with $0$ mistakes so far over the concatenation of $n$ copies of $L$ ends with a mistake count
of at least $n$.
