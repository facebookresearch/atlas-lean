# Average risk of a deterministic estimator

Let $P$ be a Markov kernel from a measurable parameter space $\Theta$ to $S$, $\pi$ a measure on $\Theta$, $\delta : S \to A$ a measurable estimator and $\ell_\theta : A \to [0, \infty)$ losses with each $a \mapsto \ell_\theta(a)$ measurable. Then the average (Bayes) risk of the deterministic decision kernel of $\delta$ under the prior $\pi$ equals $\int R(\theta)\,d\pi(\theta)$, where $R(\theta) = \int\ell_\theta(\delta(s))\,dP_\theta(s)$ is the frequentist risk, in $[0, \infty]$.
