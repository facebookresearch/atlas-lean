# MAP classifiers are posterior argmax classifiers

Let the set $C$ of classes be countable
and nonempty with measurable singletons, let the observation space $\mathcal X$ be countable with
measurable singletons, let $P$ be a Markov kernel from $C$ to $\mathcal X$ and $\pi$ a finite
measure on $C$, and write $P \circ \pi$ for the marginal measure on $\mathcal X$. If
$f : \mathcal X \to C$ assigns to every observation $x$ with $(P \circ \pi)(\{x\}) \ne 0$ a
maximum a posteriori class for $x$ under $P$ and $\pi$, then $f$ is a posterior argmax
classifier for $P$ and $\pi$.

Since posterior argmax classifiers attain the Bayes risk for the 0-1 loss, MAP classification is
Bayes optimal; observations of zero evidence may be classified arbitrarily.
