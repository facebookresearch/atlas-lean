# Systematic-scan Gibbs sampler

Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every
$x$. For a list $l = (i_1, \dots, i_n)$ of coordinates, the systematic-scan Gibbs sampler is the
Markov kernel on configurations that applies the Gibbs updates of the coordinates
$i_1, i_2, \dots, i_n$ in this order; for the empty list it is the identity kernel.
