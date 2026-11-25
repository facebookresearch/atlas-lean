# Zero prior or zero likelihood gives zero posterior

Let $\Theta$ be a finite set of hypotheses, $\pi : \Theta \to \mathbb{R}$ prior weights and $L : \Theta \to \mathbb{R}$ likelihood weights; write $E(\pi, L) = \sum_\theta \pi(\theta) L(\theta)$ for the evidence and $\pi_L(\theta) = \pi(\theta)L(\theta)/E(\pi, L)$ for the Bayes update (the zero function when $E(\pi, L) = 0$, by $x/0 = 0$). If $\pi(\theta) L(\theta) = 0$, then $\pi_L(\theta) = 0$.
