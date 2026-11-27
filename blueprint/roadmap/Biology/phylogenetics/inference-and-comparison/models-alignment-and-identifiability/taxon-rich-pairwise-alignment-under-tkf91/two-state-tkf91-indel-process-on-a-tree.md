# Two-state TKF91 insertion–deletion process on a tree

**Definition.** Fix rates $\eta,\lambda,\mu\in(0,\infty)$ and letter frequencies $(\pi_0,\pi_1)$ with $\pi_0+\pi_1=1$. The (two-state) **TKF91 process** is the continuous-time Markov chain on

$$\mathcal{S}=\{\bullet\}\otimes\bigcup_{M\ge0}\{0,1\}^M$$

(binary sequences preceded by an *immortal link* $\bullet$; $M = 0$ gives the empty word, the state with the immortal link alone) in which, independently:

- each site is *substituted* at rate $\eta$, its new digit being $0$ or $1$ with probabilities $\pi_0,\pi_1$;
- each site is *deleted* at rate $\mu$;
- each site and the immortal link give birth at rate $\lambda$ to a new site placed immediately to its right, with digit drawn from $(\pi_0,\pi_1)$ (an *insertion*).

**Proposition.** If $\mu>\lambda$, the sequence length $|\sigma|$ has stationary distribution

$$\gamma_M=\Bigl(1-\frac{\lambda}{\mu}\Bigr)\Bigl(\frac{\lambda}{\mu}\Bigr)^{M},\qquad M\in\mathbb{Z}_{\ge0},$$

and the stationary sequence has i.i.d. sites with law $(\pi_0,\pi_1)$ given its length. The total rate of leaving a state $\sigma$ (to sequences one substitution, insertion or deletion away) is

$$\lambda^\ast(\sigma)=\lambda\,(|\sigma|+1)+\mu\,|\sigma|+\eta\pi_1|\sigma|_0+\eta\pi_0|\sigma|_1 ,$$

where $|\sigma|_b$ counts digits equal to $b$. In particular $\mathbb{P}(|\sigma|>L)=(\lambda/\mu)^{L+1}$ under stationarity.

On a rooted ultrametric tree with edge lengths $t_e$, the root sequence is drawn from stationarity and the process runs independently along each edge from the parent's sequence; stationarity then holds at every point of the tree. Two sites in different sequences are *homologous* if they descend from a common ancestral site through substitutions only, and a *true alignment* puts exactly the homologous pairs in common columns.

## Expansion

Ignoring substitutions, the length performs a linear birth–death chain with birth rate $\lambda(M+1)$ (the immortal link keeps the empty sequence from being absorbing) and death rate $\mu M$; detailed balance $\gamma_{M+1}\mu(M+1)=\gamma_M\lambda(M+1)$ gives the geometric law, which is normalizable exactly when $\lambda<\mu$. The exit rate counts $|\sigma|+1$ possible insertion points, $|\sigma|$ deletions, and only substitutions that change a digit ($0\to1$ at rate $\eta\pi_1$, $1\to0$ at rate $\eta\pi_0$). The geometric length tail is what lets alignment analyses truncate sequence lengths at $O(\log(1/\delta))$ with failure probability $\delta^2$.

## Sources

- Brandon Legried and Sebastien Roch, "Pairwise sequence alignment at arbitrarily large evolutionary distance", The Annals of Applied Probability 34 (2024), 2714–2732, <https://doi.org/10.1214/23-aap2009>; numbering as in arXiv:2207.12543: Section 2.1: Definition 1, the stationary length distribution in equation (1), and the exit-rate formula, Lemma 6 in the appendix.
- J. L. Thorne, H. Kishino, J. Felsenstein, "An evolutionary model for maximum likelihood alignment of DNA sequences", Journal of Molecular Evolution 33 (1991) 114–124, <https://doi.org/10.1007/BF02193625>.
