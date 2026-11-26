# Sequential Bayes updating

For a finite set $\Theta$, prior weights $\pi$ and a list $L_1, \dots, L_k$ of likelihood weights, the sequential posterior updates $\pi$ on the observations one at a time in list order: it is $\pi$ for the empty list, and for the list $L_1, L_2, \dots, L_k$ it is the sequential posterior of the updated prior $\pi_{L_1}$ on $L_2, \dots, L_k$, where $\pi_L(\theta) = \pi(\theta)L(\theta)/\sum_{\theta'}\pi(\theta')L(\theta')$ is the Bayes update of $\pi$ by $L$, taken to be $0$ when $\sum_{\theta'}\pi(\theta')L(\theta') = 0$.
