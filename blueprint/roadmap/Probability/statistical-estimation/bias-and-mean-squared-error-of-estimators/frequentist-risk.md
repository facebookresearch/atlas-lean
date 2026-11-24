# Frequentist risk

Let $S$ be a measurable space, $\delta : S \to A$ a decision rule,
$(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$, and
$\ell : \Theta \times A \to [0, \infty)$ a loss such that $x \mapsto \ell(\theta, \delta(x))$ is
$P_\theta$-integrable for every $\theta \in \Theta$. The frequentist risk of $\delta$ is the
function $\Theta \to \mathbb{R}$ given by
$R(\theta, \delta) = \int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$.

The rule $\delta$ does not depend on $\theta$, and the action space $A$ may differ from $\Theta$.
No prior, kernel or optimality criterion enters.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, §7.3.4, equation (7.3.16); the integrability hypothesis is the expectation domain of Chapter 2 Definition 2.2.1.
