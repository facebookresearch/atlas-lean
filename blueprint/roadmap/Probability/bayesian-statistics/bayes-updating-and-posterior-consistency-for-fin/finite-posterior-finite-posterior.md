# Updating twice is updating on the product likelihood

Let $\Theta$ be a finite set of hypotheses, $\pi : \Theta \to \mathbb{R}$ prior weights and $L : \Theta \to \mathbb{R}$ likelihood weights; write $E(\pi, L) = \sum_\theta \pi(\theta) L(\theta)$ for the evidence and $\pi_L(\theta) = \pi(\theta)L(\theta)/E(\pi, L)$ for the Bayes update (the zero function when $E(\pi, L) = 0$, by $x/0 = 0$). If $E(\pi, L_1) \ne 0$, then updating on $L_1$ and then on $L_2$ is updating once on $L_1 L_2$: $(\pi_{L_1})_{L_2} = \pi_{L_1 L_2}$.
