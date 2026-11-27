# Perceptron run

Let $K$ be a commutative ring with a linear order and $\iota$ a finite type.
The run of the perceptron over a finite list $L$ of labelled examples $(x, y)$, with
$x \in K^\iota$ and $y$ a Boolean, from weights $w \in K^\iota$ with $m \in \mathbb{N}$ mistakes so
far is the pair of final weights and final mistake count obtained by applying the perceptron step
to each example of $L$ in order, starting from the state $(w, m)$.
