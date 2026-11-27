# The causal Markov condition

**The causal Markov condition** (Pearl, *Statistics Surveys* 2009, Theorem 1, eq. (15);
Pearl and Verma 1991): let $M$ be a Markovian structural causal model on the nodes
$0, \dots, n - 1$ with values in a nonempty set $\alpha$ and disturbances in a finite set. The
law of $M$ factorizes over its causal diagram: it is the joint distribution of the
[causal network](to-bayes-net.md) of $M$, the product over the nodes of the probability that the
node's equation produces its value from the values of its parents.

The proof writes the indicator of $X(u) = x$ as the product over the nodes of the indicators
that $x$ satisfies each structural equation ([uniqueness of the solution](solve-eq-iff.md)), and
then exchanges the sum over the independent disturbances with the product over the nodes.
