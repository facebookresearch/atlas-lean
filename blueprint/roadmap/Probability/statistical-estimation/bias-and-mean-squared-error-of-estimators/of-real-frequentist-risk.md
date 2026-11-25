# Finite and extended frequentist risk agree

Let $\Theta$ and $A$ be sets, let
$(P_\vartheta)_{\vartheta \in \Theta}$ be a family of probability measures on a measurable space
$S$, let $\delta : S \to A$ be a decision rule and $\ell : \Theta \times A \to [0, \infty)$ a
loss, and suppose $x \mapsto \ell(\vartheta, \delta(x))$ is $P_\vartheta$-integrable for every
$\vartheta \in \Theta$. Then for every $\theta \in \Theta$ the extended frequentist risk
$\int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$, computed in $[0, \infty]$, is finite and equals
the frequentist risk of $\delta$ at $\theta$.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, §7.3.4, equation (7.3.16) (risk function).
