# Posterior class probability in the Poisson mixture

Let $\iota$ be a finite set of classes, let $w, \lambda : \iota \to \mathbb{R}$ be prior weights and class rates, let $E$ be real and $o$ a natural number. The posterior of class $c \in \iota$ is

$$P(c \mid o) = \frac{w_c\, L(\lambda_c E, o)}{\sum_{c' \in \iota} w_{c'}\, L(\lambda_{c'} E, o)},$$

where $L$ is the [Poisson likelihood](poisson-lik.md), with the convention $x/0 = 0$. When the prior weights are nonnegative, the rates and $E$ are nonnegative and the denominator is positive, it is the posterior probability of class $c$ given $o$. For a gene with $o$ observed and $E$ expected loss-of-function variants, pLI is this posterior at the class with the smallest rate.
