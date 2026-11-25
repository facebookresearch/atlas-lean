# Data-processing inequality

Let $X, Y, Z$ be measurable spaces and $\mu$ a probability measure on $X \times Y$, the joint law of $(X, Y)$; mutual information is the Kullback–Leibler divergence of a joint law from the product of its marginals, in bits, with values in $[0, \infty]$.
If $Z$ is produced from $Y$ by a Markov kernel $\kappa$ from $Y$ to $Z$ that does not see $X$ (a Markov chain
$X \to Y \to Z$), so that $(X, Z)$ has the law obtained by applying $\kappa$ to the second coordinate under $\mu$,
then $I(X; Z) \le I(X; Y)$.
