# Evidence of a second observation under the first posterior

Let $\Theta$ be a finite set of hypotheses, $\pi : \Theta \to \mathbb{R}$ prior weights and $L : \Theta \to \mathbb{R}$ likelihood weights; write $E(\pi, L) = \sum_\theta \pi(\theta) L(\theta)$ for the evidence and $\pi_L(\theta) = \pi(\theta)L(\theta)/E(\pi, L)$ for the Bayes update (the zero function when $E(\pi, L) = 0$, by $x/0 = 0$). For likelihood weights $L_1, L_2$,

$$E(\pi_{L_1}, L_2) = \frac{E(\pi, L_1 L_2)}{E(\pi, L_1)},$$

with no hypothesis: when $E(\pi, L_1) = 0$ both sides are $0$.
